#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Record what each model specifies before agents edit it, and compare it afterwards.

A model's surface is a mapping from item name to a canonical value. Every tool
uses one rule to compare surfaces: a removed item or a changed value is a
change, and so is an added item whose kind narrows what is checked.

  .statements  Lean. The toolchain, and each declaration's kind, type hash and value hash.
               Added declarations are allowed.
  .matrix      TLA+. Each run's effective checks and each reach check's selected inputs,
               and the normalized definitions of Spec,
               of each operator a check or reach line names, and of the operators those
               reference through local EXTENDS. Local INSTANCE substitutions retain their whole module tree.
  .rs          Kani. Each qualified harness name with the #[cfg(...)] attributes other
               than cfg(kani), and the #[cfg_attr(..., cfg(...))] ones, on it, its enclosing
               items, the file and each out-of-line mod declaration that leads to the file, and each kani::assume, kani::any_where, kani::cover! and
               #[kani::stub] with its owning free function, under inline modules. Unsupported owners fail. Added covers and harnesses are allowed.
               Added assumes and stubs are changes.

Usage:
  baseline.py record <record-file> <model-file>...   record these files, keep the other entries
  baseline.py compare <record-file>                  exit 1 when a recorded file changed
  baseline.py move <record-file> <old> <new> [--module OLD NEW]
                                                     compare old's entry with new from now on

Compare prints UNCHANGED or CHANGED per file, indented lines for each item that
changed, and a SUMMARY line. Move prints MOVED; it reads only the record, never
the new file, and with --module renames the recorded Kani owners under module
OLD to sit under NEW. Exit codes: 0 unchanged, 1 changed or a record or model
file that fails to parse, 2 usage error.
"""
import argparse
import hashlib
import json
import re
import sys
from pathlib import Path
from typing import NamedTuple

sys.dont_write_bytecode = True

import runner
import tlc
from lean_records import read_record as read_lean_record

FORMAT = 2
NARROWING = {"lean": (), "tla": (), "kani": ("assume", "stub")}
KINDS = {".statements": "lean", ".matrix": "tla", ".rs": "kani"}
STRING = re.compile(r'"(?:\\.|[^"\\])*"', re.DOTALL)


def collapse(text, literals=None):
    if literals is None:
        literals = (match.span() for match in STRING.finditer(text))
    parts, end = [], 0
    for start, stop in literals:
        parts.extend((re.sub(r"\s+", " ", text[end:start]), text[start:stop]))
        end = stop
    parts.append(re.sub(r"\s+", " ", text[end:]))
    return "".join(parts).strip()


class Surface(dict):
    def add(self, name, value=""):
        candidate, count = name, 1
        while candidate in self:
            count += 1
            candidate = f"{name} #{count}"
        self[candidate] = value
        return candidate


def lean_surface(path):
    record = read_lean_record(path)
    surface = Surface()
    surface.add("toolchain", record["toolchain"])
    for entry in record["declarations"]:
        surface.add(f"declaration {entry['name']}", f"{entry['kind']} {entry['typeHash']} {entry['valueHash'] or '-'}")
    return surface


def tla_text(text):
    """Columns can group TLA+ conjunctions and disjunctions across lines."""
    lines = [line.rstrip() for line in text.splitlines() if line.strip()]
    return "\n".join(lines) if len(lines) > 1 else collapse("".join(lines))


def blank_tla_comments(text):
    out, i = [], 0
    while i < len(text):
        if text[i] == '"':
            string = STRING.match(text, i)
            if string is None:
                raise ValueError("unterminated TLA+ string")
            out.append(string[0])
            i = string.end()
        elif text.startswith("(*", i):
            start, depth = i, 0
            while i < len(text):
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                    if not depth:
                        break
                else:
                    i += 1
            # A following token keeps its source column, even after a nested comment.
            out.append(re.sub(r"[^\s]", " ", text[start:i]))
        elif text.startswith("\\*", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


DEFINITION = re.compile(r"(?:LOCAL\s+)?(\w*[A-Za-z]\w*)\s*(?:\((?:[^()]|\([^()]*\))*\)|\[(?:[^\[\]]|\[[^\[\]]*\])*\])?\s*==")
MODULE_LEVEL = re.compile(r"-{4,}|={4,}|(?:EXTENDS|VARIABLES?|CONSTANTS?|ASSUME|ASSUMPTION|AXIOM|THEOREM|LEMMA|PROPOSITION|COROLLARY|INSTANCE|RECURSIVE|USE|HIDE)\b")
IDENTIFIER = re.compile(r"\w*[A-Za-z]\w*")
SUBSCRIPT = r"_(\w+|<<[^>]*>>)"
SPEC_ACTIONS = re.compile(rf"\[\]\[[^\]]*\]{SUBSCRIPT}|[WS]F{SUBSCRIPT}\s*\([^()]*\)")
# The prefix that joins a subscript, such as vars in WF_vars, [A]_vars or <<A>>_vars, to one token.
SUBSCRIPT_PREFIX = re.compile(r"\b[WS]F_|\]_|>>_")


def begins_in_column_zero(line):
    return line[:1].strip() != ""


DEFINITION_TOKENS = re.compile(r"\b(?:LET|IN)\b|(?<!=)==(?!=)")


def has_unplaced_definition(code):
    """Return whether a definition can lie outside the column-0 headers that tla_definitions splits on.

    An indented `==` inside an open LET defines a LET-local operator. Any other indented `==`, a line
    that starts with `==`, or a column-0 header while a LET is open can define a module operator.
    """
    open_lets = 0
    for line in code.split("\n"):
        indented = not begins_in_column_zero(line)
        if open_lets and not indented and ("==" in line or MODULE_LEVEL.match(line)):
            return True
        for token in DEFINITION_TOKENS.finditer(line):
            if token[0] == "LET":
                open_lets += 1
            elif token[0] == "IN":
                open_lets = max(open_lets - 1, 0)
            elif not open_lets and (indented or token.start() == 0):
                return True
    return False


def tla_definitions(text):
    found, unreadable, name, lines = {}, set(), None, []
    for line in text.split("\n"):
        if begins_in_column_zero(line):
            match = DEFINITION.match(line)
            header = None if match or MODULE_LEVEL.match(line) or "==" not in line else collapse(line.partition("==")[0])
            if match or header or MODULE_LEVEL.match(line):
                if name:
                    found[name] = tla_text("\n".join(lines))
                name, lines = (match[1] if match else header), ([line] if match or header else [])
                if header:
                    unreadable.add(header)
                continue
        if name:
            lines.append(line)
    if name:
        found[name] = tla_text("\n".join(lines))
    return found, unreadable


EXTENDS = re.compile(r"\bEXTENDS\s+(\w+(?:\s*,\s*\w+)*)")
INSTANCE = re.compile(r"\bINSTANCE\s+(\w+)")
INDENTED_DEFINITION = re.compile(r"^[ \t]*" + DEFINITION.pattern, re.MULTILINE)


def tla_module_surface(directory, spec, operators):
    """Resolve operator references in the module that defines them, including sibling imports."""
    root = Path(spec)
    texts, bodies, scopes, exports = {}, {}, {}, {}
    required, visiting = set(), set()
    whole_modules = False

    def load(path):
        nonlocal whole_modules
        if path in exports:
            return exports[path]
        if path in visiting:
            raise ValueError(f"cyclic TLA+ import at {path}")
        visiting.add(path)
        text = blank_tla_comments(tlc.read_raw(directory / path))
        texts[path] = text
        code = STRING.sub('""', text)
        if has_unplaced_definition(code):
            whole_modules = True
        scope = {}
        for group in EXTENDS.findall(code):
            for name in IDENTIFIER.findall(group):
                sibling = path.with_name(f"{name}.tla")
                if (directory / sibling).is_file():
                    scope.update(load(sibling))
        for name in INSTANCE.findall(code):
            sibling = path.with_name(f"{name}.tla")
            if (directory / sibling).is_file():
                whole_modules = True
                load(sibling)
        definitions, unreadable = tla_definitions(text)
        for name, body in definitions.items():
            key = (path, name)
            bodies[key] = body
            scope[name] = key
        required.update((path, name) for name in unreadable)
        scopes[path] = scope
        exports[path] = {name: key for name, key in scope.items() if not re.match(r"LOCAL\s", bodies[key])}
        visiting.remove(path)
        return exports[path]

    load(root)
    surface = {f"imports {spec}": sorted(str(path) for path in texts if path != root)}
    fallback_names = set()
    if whole_modules:
        fallback_names = {match[1] for text in texts.values() for match in INDENTED_DEFINITION.finditer(text)}
    for name in sorted({"Spec", *operators}):
        if name in scopes[root]:
            required.add(scopes[root][name])
        elif name.rpartition("!")[2] not in fallback_names:
            raise ValueError(f"{name} is named in the {spec} section but no definition was found in it or its local imports")
    if whole_modules:
        # Preserve substitutions and dependencies whose operator scope cannot be resolved.
        for path, text in texts.items():
            surface[f"module text {spec} | {path}"] = tla_text(text)
        return surface

    seen = set()
    while required:
        key = required.pop()
        if key in seen:
            continue
        seen.add(key)
        owner, name = key
        surface[f"definition {owner} {name}"] = bodies[key]
        header, _, body = bodies[key].partition("==")
        body = STRING.sub('""', body)
        if key == scopes[root]["Spec"]:
            # Keep the subscript, such as vars: it decides which steps may stutter and what fairness requires.
            body = SPEC_ACTIONS.sub(lambda form: f" {form[1] or form[2]} ", body)
        body = SUBSCRIPT_PREFIX.sub(" ", body)
        if "[" in header:
            # A function definition such as F[x \in S] == ... references S in its header.
            body = f"{header} {body}"
        required.update(scopes[owner][word] for word in IDENTIFIER.findall(body) if word in scopes[owner])
    return surface


def tla_surface(path):
    surface = Surface()
    surface.add("TLA+ layout version", 1)
    specs = {}
    plan = tlc.MatrixPlan(path)
    tasks = plan.checked_tasks()
    for spec in plan.specs:
        surface.add(f"spec {spec}")
        specs.setdefault(spec, set())
    for task in tasks:
        if task.reach:
            surface.add(f"reach {task.spec} {task.reach.operator} | {collapse(task.reach.match)}",
                        {"run": collapse(task.run.label), "constants": collapse(task.run.constants)})
            specs[task.spec].add(task.reach.operator)
        else:
            run = surface.add(f"run {task.spec} {collapse(task.run.label)}", collapse(task.run.constants))
            for check in task.checks:
                for name in check.names:
                    surface.add(f"check {task.spec} {check.kind} {name} | [{run}]")
                specs[task.spec].update(check.names)
    for spec, operators in specs.items():
        source = path.parent / spec
        if not source.is_file():
            raise ValueError(f"{path}: spec {spec} not found")
        surface.update(tla_module_surface(path.parent, spec, operators))
    return surface


class RustSource(NamedTuple):
    uncommented: str
    without_comments_or_strings: str
    literals: list


def rust_masks(source):
    text, mask = list(source), list(source)
    literals = []

    def blank(start, end, *, both):
        for i in range(start, end):
            if source[i] != "\n":
                mask[i] = " "
                if both:
                    text[i] = " "

    i = 0
    while i < len(source):
        if source.startswith("//", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            blank(i, end, both=True)
            i = end
        elif source.startswith("/*", i):
            depth, start = 0, i
            while i < len(source):
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                    if not depth:
                        break
                else:
                    i += 1
            blank(start, i, both=True)
        elif raw := re.compile(r'(?<!\w)[bc]?r(#*)"').match(source, i):
            close = source.find('"' + raw[1], raw.end())
            content_end = len(source) if close < 0 else close
            blank(raw.end(), content_end, both=False)
            i = content_end + 1 + len(raw[1])
            literals.append((raw.start(), min(i, len(source))))
        elif source[i] == '"':
            opening = i
            start = i = i + 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            blank(start, min(i, len(source)), both=False)
            i += 1
            literals.append((opening, min(i, len(source))))
        elif char := re.compile(r"'(?:\\.[^']*|[^'\\])'").match(source, i):
            blank(char.start() + 1, char.end() - 1, both=False)
            i = char.end()
            literals.append(char.span())
        else:
            i += 1
    return RustSource("".join(text), "".join(mask), literals)


def after_closing(mask, opener):
    closer = {"(": ")", "[": "]", "{": "}"}[mask[opener]]
    depth = 0
    for i in range(opener, len(mask)):
        depth += (mask[i] == mask[opener]) - (mask[i] == closer)
        if not depth:
            return i + 1
    raise ValueError(f"unbalanced {mask[opener]} at offset {opener}")


class RustFunction(NamedTuple):
    name: str
    start: int
    body: int
    end: int


RUST_ITEM = re.compile(r"\b(fn|mod)\s+((?:r#)?\w+)\b")


def rust_functions(mask):
    """Locate free functions, inline modules and out-of-line `mod name;` declarations; leave macro and other item
    bodies opaque.

    A declaration's body is its `;`.
    """
    functions, modules, opaque, declarations, counts = [], [], [], [], {}

    def walk(start, end, namespace=(), in_function=False):
        i, boundary, item = start, start, None
        while i < end:
            if match := RUST_ITEM.match(mask, i):
                item = (match[1], match[2])
                i = match.end()
            elif mask[i] in "([":
                stop = after_closing(mask, i)
                if mask[boundary:i].rstrip().endswith("!"):
                    opaque.append((i, stop))
                i = stop
            elif mask[i] == "{":
                stop = after_closing(mask, i)
                header = mask[boundary:i].rstrip()
                macro = header.endswith("!") or bool(re.search(r"\bmacro_rules\s*!\s*\w+\s*$", header))
                if item and not macro:
                    kind, name = item
                    qualified = (*namespace, name)
                    if kind == "fn":
                        owner = "::".join(qualified)
                        counts[owner] = counts.get(owner, 0) + 1
                        suffix = f"[{counts[owner]}]" if counts[owner] > 1 else ""
                        functions.append(RustFunction(owner + suffix, boundary, i, stop))
                    else:
                        modules.append(RustFunction("::".join(qualified), boundary, i, stop))
                    walk(i + 1, stop - 1, qualified, kind == "fn")
                elif in_function and not macro and not re.search(r"\b(?:impl|trait|struct|enum|union|extern|macro)\b", header):
                    walk(i + 1, stop - 1, namespace, True)
                else:
                    opaque.append((i, stop))
                i = boundary = stop
                item = None
            else:
                if mask[i] == ";":
                    if item and item[0] == "mod" and not in_function:
                        declarations.append(RustFunction("::".join((*namespace, item[1])), boundary, i, i + 1))
                    boundary, item = i + 1, None
                i += 1

    walk(0, len(mask))
    return functions, modules, opaque, declarations


KANI_ATTRIBUTE = r"#\s*\[\s*(?:cfg_attr\s*\(\s*kani\s*,\s*)?kani\s*::\s*"
MACROS = (
    ("assume", re.compile(r"\bkani\s*::\s*assume\s*\(")),
    ("assume", re.compile(r"\bkani\s*::\s*any_where\s*(?:::\s*<[^<>]*(?:<[^<>]*>[^<>]*)*>\s*)?\(")),
    ("cover", re.compile(r"\bkani\s*::\s*cover\s*!\s*\(")),
    ("stub", re.compile(KANI_ATTRIBUTE + r"stub\s*\(")),
)
PROOF = re.compile(KANI_ATTRIBUTE + r"proof(?:_for_contract\s*\([^)]*\))?\s*\)?\s*\]")
KANI_TOKEN = re.compile(r"\bkani\s*::\s*(?:assume|any_where|cover|stub|proof)\w*\b")
OUTER_CFG, INNER_CFG = (re.compile(rf"#\s*{bang}\[\s*cfg(?:_attr)?\s*\(") for bang in ("", r"!\s*"))
INNER_ATTRIBUTE = re.compile(r"[\s\ufeff]*#\s*!\s*\[")
RENAMING_IMPORT = re.compile(r"\buse\s+[^;]*?(?<![\w:])(?:::\s*)?kani\b[^;]*?(?:\bas\b|\*|\b(?:assume|any_where|cover|stub|proof)\w*\b)|\bextern\s+crate\s+kani\s+as\b")


def cfg_guards(source, items):
    """Return the cfg attributes other than cfg(kani), and the cfg_attr ones that apply a cfg, on each (start, body)
    item and at the start of its body.

    A body of -1 stands for the file, which has only inner attributes, and a body at a `;` for an out-of-line `mod`
    declaration, which has none.
    """
    text, mask = source.uncommented, source.without_comments_or_strings
    guards = []

    def read(pattern, start, stop):
        for match in pattern.finditer(mask, start, stop):
            opener = mask.index("[", match.start())
            attribute = rust_masks(text[opener + 1:after_closing(mask, opener) - 1])
            guard = collapse(attribute.uncommented, attribute.literals)
            compact = re.sub(r"\s+", "", guard)
            if compact.startswith("cfg(") and compact != "cfg(kani)" or re.search(r"[(,]cfg\(", compact.removeprefix("cfg_attr(")):
                guards.append(guard)

    for start, body in items:
        if body >= 0:
            read(OUTER_CFG, start, RUST_ITEM.search(mask, start, body).start())
        if body >= 0 and mask[body] == ";":
            continue
        first = inner = body + 1
        while attribute := INNER_ATTRIBUTE.match(mask, inner):
            inner = after_closing(mask, attribute.end() - 1)
        read(INNER_CFG, first, inner)
    return " ".join(guards)


def declaration_guards(path):
    """Return the guards on the out-of-line `mod` declarations that lead to path, outermost first.

    The search follows Rust's default module layout: a lib.rs, main.rs or mod.rs declares the files in its own
    directory, and any other x.rs those in x/, each under the directories of the inline modules around the
    declaration. It climbs to the first directory that holds a lib.rs, main.rs or Cargo.toml.
    """
    if path.name in ("lib.rs", "main.rs"):
        return ""
    names = [path.parent.name] if path.name == "mod.rs" else [path.stem]
    directory = path.parent.parent if path.name == "mod.rs" else path.parent
    guards = []
    while True:
        for parent in (directory / "lib.rs", directory / "main.rs", directory / "mod.rs", directory.parent / f"{directory.name}.rs"):
            if parent == path or not parent.is_file():
                continue
            try:
                source = rust_masks(parent.read_text(encoding="utf-8"))
                _, modules, _, declarations = rust_functions(source.without_comments_or_strings)
            except ValueError as error:
                raise ValueError(f"{parent}: {error}") from None
            for declaration in declarations:
                if declaration.name.replace("r#", "") == "::".join(names):
                    enclosing = sorted((module for module in modules if module.start <= declaration.start < module.end), key=lambda module: module.start)
                    items = [(0, -1)] + [(module.start, module.body) for module in enclosing] + [(declaration.start, declaration.body)]
                    guards += [declaration_guards(parent), cfg_guards(source, items)]
        if directory.parent == directory or any((directory / name).exists() for name in ("lib.rs", "main.rs", "Cargo.toml")):
            return " ".join(filter(None, guards))
        names.insert(0, directory.name)
        directory = directory.parent


def kani_surface(path):
    source = rust_masks(path.read_text(encoding="utf-8"))
    text, mask = source.uncommented, source.without_comments_or_strings
    if renaming := RENAMING_IMPORT.search(mask):
        raise ValueError(f"{path}: '{collapse(renaming[0])}' brings a Kani assumption, cover, stub or harness attribute in under another name; write each as kani::<name> so the record can read it")
    functions, modules, opaque, _ = rust_functions(mask)
    declared = declaration_guards(path)

    def owner_at(position, *, attribute=False):
        if not any(start <= position < end for start, end in opaque):
            for function in reversed(functions):
                if function.start <= position < function.end and (position < function.body if attribute else position > function.body):
                    return function
        line = mask.count("\n", 0, position) + 1
        raise ValueError(f"{path}:{line}: cannot identify a function owner; write Kani forms in free functions under inline modules, outside macro definitions and impl or trait bodies")

    surface = Surface()
    spans, read = [], []
    for kind, pattern in MACROS:
        for match in pattern.finditer(mask):
            end = after_closing(mask, match.end() - 1)
            read.append((match.start(), end))
            argument = rust_masks(text[match.end():end - 1])
            owner = owner_at(match.start(), attribute=kind == "stub").name
            spans.append((match.start(), f"{kind} {collapse(argument.uncommented, argument.literals)} in {owner}", ""))
    for match in PROOF.finditer(mask):
        read.append(match.span())
        harness = owner_at(match.start(), attribute=True)
        enclosing = sorted((item for item in functions + modules if item.start <= harness.start and harness.end <= item.end), key=lambda item: item.start)
        guards = " ".join(filter(None, (declared, cfg_guards(source, [(0, -1)] + [(item.start, item.body) for item in enclosing]))))
        spans.append((match.start(), f"harness {harness.name}", guards))
    for token in KANI_TOKEN.finditer(mask):
        if not any(start <= token.start() < end for start, end in read):
            line = mask.count("\n", 0, token.start()) + 1
            raise ValueError(f"{path}:{line}: '{collapse(token[0])}' is in a form the record cannot read; write kani::assume(...), kani::any_where(...), kani::cover!(...), #[kani::stub(...)] or #[kani::proof], alone or under #[cfg_attr(kani, ...)]")
    for _, item, guards in sorted(spans):
        surface.add(item, guards)
    return surface


SURFACES = {"lean": lean_surface, "tla": tla_surface, "kani": kani_surface}


def digest(surface):
    return hashlib.sha256(json.dumps(surface, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()


def read_record(path):
    record = json.loads(path.read_text(encoding="utf-8"))
    models = record.get("models") if isinstance(record, dict) else None
    if not isinstance(models, dict) or record.get("format") != FORMAT:
        raise ValueError(f"{path}: unsupported record format; run record with a new record file")
    for model, entry in models.items():
        if not isinstance(entry, dict) or entry.get("kind") not in SURFACES or not isinstance(entry.get("surface"), dict):
            raise ValueError(f"{path}: malformed entry for {model}")
    return models


def write_record(path, models):
    path.parent.mkdir(parents=True, exist_ok=True)
    runner.atomic_write(path, json.dumps({"format": FORMAT, "models": models}, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def record(record_path, files):
    for file in files:
        if file.suffix not in KINDS:
            print(f"usage: {file} has no model surface; expected one of {', '.join(KINDS)}")
            return 2
    models = read_record(record_path) if record_path.exists() else {}
    updates = {}
    for file in files:
        kind = KINDS[file.suffix]
        surface = SURFACES[kind](file.resolve())
        updates[str(file.resolve())] = {"kind": kind, "digest": digest(surface), "surface": surface}
    for model, entry in updates.items():
        print(f"RECORDED {model} {entry['digest']}")
        previous = models.get(model, {}).get("digest")
        if previous and previous != entry["digest"]:
            print(f"  previous {previous}")
    write_record(record_path, {**models, **updates})
    return 0


KANI_KEY = re.compile(r"(harness |(?:assume|cover|stub) .* in )(\S+)( #\d+)?", re.DOTALL)


def renamed(surface, old_module, new_module):
    """Rewrite each Kani owner under old_module to sit under new_module, where `crate` is the file's root."""
    old, new = ([] if path == "crate" else path.split("::") for path in (old_module, new_module))
    result = {}
    for name, value in surface.items():
        head, owner, duplicate = KANI_KEY.fullmatch(name).groups()
        parts = owner.split("::")
        if parts[:len(old)] == old:
            owner = "::".join(new + parts[len(old):])
        result[f"{head}{owner}{duplicate or ''}"] = value
    if len(result) != len(surface):
        raise ValueError(f"renaming {old_module} to {new_module} merges recorded items")
    return result


def move(record_path, old_file, new_file, module):
    models = read_record(record_path) if record_path.is_file() else {}
    old, new = str(old_file.resolve()), str(new_file.resolve())
    if old not in models:
        print(f"usage: {old} has no record entry; record it before the move")
        return 2
    kind = models[old]["kind"]
    if KINDS.get(new_file.suffix) != kind:
        print(f"usage: {new} is not a {kind} model file")
        return 2
    if module and kind != "kani":
        print("usage: --module applies only to a Kani harness file")
        return 2
    surface = models.pop(old)["surface"]
    if module:
        surface = renamed(surface, *module)
    if new in models:
        if overlap := surface.keys() & models[new]["surface"].keys():
            raise ValueError(f"{new} already records {', '.join(sorted(overlap))}")
        surface = {**models[new]["surface"], **surface}
    models[new] = {"kind": kind, "digest": digest(surface), "surface": surface}
    write_record(record_path, models)
    print(f"MOVED {old} -> {new}")
    return 0


def differences(kind, old, new):
    lines = []
    if kind == "tla" and not any(name.startswith("imports ") for name in old):
        lines.append("  previous baseline did not track imported modules; review and record this matrix again")
    if kind == "tla" and "TLA+ layout version" not in old:
        lines.append("  previous baseline did not preserve TLA+ layout; review and record this matrix again")
    for name in old:
        if name not in new:
            lines.append(f"  removed {name}")
        elif old[name] != new[name]:
            lines += [f"  changed {name}", f"    old: {old[name]}", f"    new: {new[name]}"]
    lines += [f"  added {name}" for name in new if name not in old and name.split(" ", 1)[0] in NARROWING[kind]]
    return lines


def compare(record_path):
    if not record_path.is_file():
        print(f"usage: record file {record_path} does not exist; run record first")
        return 2
    models = read_record(record_path)
    changed = 0
    for model, entry in models.items():
        try:
            if not Path(model).is_file():
                lines = ["  file is missing"]
            else:
                lines = differences(entry["kind"], entry["surface"], SURFACES[entry["kind"]](Path(model)))
        except (OSError, ValueError, KeyError, TypeError) as error:
            lines = [f"  FAIL {error}"]
        changed += bool(lines)
        print(f"{'CHANGED' if lines else 'UNCHANGED'} {model}")
        if lines:
            print("\n".join(lines))
    print(f"SUMMARY {len(models) - changed} unchanged, {changed} changed")
    return int(changed > 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    recording = commands.add_parser("record", help="record or update the entries for these model files")
    recording.add_argument("record_file", type=Path)
    recording.add_argument("models", nargs="+", type=Path)
    commands.add_parser("compare", help="compare every recorded model with its file").add_argument("record_file", type=Path)
    moving = commands.add_parser("move", help="move a model's recorded entry to the file it moved to")
    moving.add_argument("record_file", type=Path)
    moving.add_argument("old_file", type=Path)
    moving.add_argument("new_file", type=Path)
    moving.add_argument("--module", nargs=2, metavar=("OLD", "NEW"),
                        help="the Kani harnesses moved from module OLD to NEW; crate names the file's root")
    arguments = parser.parse_args()
    if arguments.command == "record":
        return record(arguments.record_file, arguments.models)
    if arguments.command == "move":
        return move(arguments.record_file, arguments.old_file, arguments.new_file, arguments.module)
    return compare(arguments.record_file)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL baseline: {error}")
        sys.exit(1)
