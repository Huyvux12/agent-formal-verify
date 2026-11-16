#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Record what each model specifies before agents edit it, and compare it afterwards.

A model's surface is a mapping from item name to a canonical value. Every tool
uses one rule to compare surfaces: a removed item or a changed value is a
change, and so is an added item whose kind narrows what is checked.

  .statements  Lean. The toolchain, and each declaration's kind, type hash and value hash.
               Added declarations are allowed.
  .matrix      TLA+. Each directive of the matrix, and the normalized definitions of Spec,
               of each operator a check or reach line names, and of the operators those
               reference, in the spec each section names. Spec is not followed into its actions.
  .rs          Kani. Each harness name, and each kani::assume, kani::any_where, kani::cover! and
               #[kani::stub] anywhere in the file. Added covers and harnesses are allowed.
               Added assumes and stubs are changes.

Usage:
  baseline.py record <record-file> <model-file>...   record these files, keep the other entries
  baseline.py compare <record-file>                  exit 1 when a recorded file changed

Compare prints UNCHANGED or CHANGED per file, indented lines for each item that
changed, and a SUMMARY line. Exit codes: 0 unchanged, 1 changed or a record or
model file that fails to parse, 2 usage error.
"""
import argparse
import hashlib
import importlib.util
import json
import re
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True

import tlc

HERE = Path(__file__).resolve().parent
FORMAT = 1
NARROWING = {"lean": (), "tla": (), "kani": ("assume", "stub")}
KINDS = {".statements": "lean", ".matrix": "tla", ".rs": "kani"}


def collapse(text):
    return " ".join(text.split())


class Surface(dict):
    def add(self, name, value=""):
        candidate, count = name, 1
        while candidate in self:
            count += 1
            candidate = f"{name} #{count}"
        self[candidate] = value


def lean_surface(path):
    spec = importlib.util.spec_from_file_location("lean_statements", HERE / "lean-statements.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    record = module.read_record(path)
    surface = Surface()
    surface.add("toolchain", record["toolchain"])
    for entry in record["declarations"]:
        surface.add(f"declaration {entry['name']}", f"{entry['kind']} {entry['typeHash']} {entry['valueHash'] or '-'}")
    return surface


def strip_tla_comments(text):
    out, i = [], 0
    while i < len(text):
        if text.startswith("(*", i):
            depth = 0
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
                    out.append("\n" if text[i] == "\n" else "")
                    i += 1
            out.append(" ")
        elif text.startswith("\\*", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


DEFINITION = re.compile(r"(?:LOCAL\s+)?([A-Za-z_]\w*)\s*(?:\((?:[^()]|\([^()]*\))*\)|\[[^\]]*\])?\s*==")
MODULE_LEVEL = re.compile(r"-{4,}|={4,}|(?:EXTENDS|VARIABLES?|CONSTANTS?|ASSUME|ASSUMPTION|AXIOM|THEOREM|LEMMA|PROPOSITION|COROLLARY|INSTANCE|RECURSIVE|USE|HIDE)\b")
IDENTIFIER = re.compile(r"[A-Za-z_]\w*")
SUBSCRIPT = r"_(?:\w+|<<[^>]*>>)"
SPEC_ACTIONS = re.compile(rf"\[\]\[[^\]]*\]{SUBSCRIPT}|[WS]F{SUBSCRIPT}\s*\([^()]*\)")


def tla_definitions(path, text):
    found, name, lines = {}, None, []
    for line in strip_tla_comments(text).split("\n"):
        if line[:1].strip():
            match = DEFINITION.match(line)
            if match or MODULE_LEVEL.match(line):
                if name:
                    found[name] = collapse(" ".join(lines))
                name, lines = (match[1], [line]) if match else (None, [])
                continue
            if "==" in line:
                raise ValueError(f"{path}: '{collapse(line)}' defines an operator in a form the record cannot read; write Name == ..., Name(a, b) == ... or Name[x \\in S] == ...")
        if name:
            lines.append(line)
    if name:
        found[name] = collapse(" ".join(lines))
    return found


def tla_closure(definitions, roots):
    seen, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        body = definitions[name].partition("==")[2]
        if name == "Spec":
            body = SPEC_ACTIONS.sub(" ", body)
        pending += [word for word in IDENTIFIER.findall(body) if word in definitions and word != name]
    return seen


def tla_surface(path):
    surface = Surface()
    sections = []
    parsed = list(tlc.directives(tlc.read_raw(path).split("\n")))
    malformed = [directive.message for directive in parsed if isinstance(directive, tlc.Malformed)]
    if malformed:
        raise ValueError(f"{path}: {'; '.join(malformed)}")
    for directive in parsed:
        if isinstance(directive, tlc.Spec):
            if not directive.path:
                raise ValueError(f"{path}: spec line has no path")
            surface.add(f"spec {directive.path}")
            sections.append((directive.path, set()))
        elif isinstance(directive, tlc.Check):
            for name in directive.names:
                surface.add(f"check {sections[-1][0]} {directive.kind} {name}")
            sections[-1][1].update(directive.names)
        elif isinstance(directive, tlc.Reach):
            surface.add(f"reach {sections[-1][0]} {directive.operator} | {collapse(directive.match)}")
            sections[-1][1].add(directive.operator)
        else:
            surface.add(f"run {sections[-1][0]} {collapse(directive.label)}", collapse(directive.constants))
    for spec, operators in sections:
        source = path.parent / spec
        if not source.is_file():
            raise ValueError(f"{path}: spec {spec} not found")
        definitions = tla_definitions(source, tlc.read_raw(source))
        for name in sorted({"Spec", *operators}):
            if name not in definitions:
                raise ValueError(f"{path}: {name} is named in the {spec} section but {source} does not define it")
        for name in sorted(tla_closure(definitions, {"Spec", *operators})):
            surface[f"definition {spec} {name}"] = definitions[name]
    return surface


def rust_masks(source):
    text, mask = list(source), list(source)

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
        elif raw := re.compile(r'(?<!\w)b?r(#*)"').match(source, i):
            close = source.find('"' + raw[1], raw.end())
            content_end = len(source) if close < 0 else close
            blank(raw.end(), content_end, both=False)
            i = content_end + 1 + len(raw[1])
        elif source[i] == '"':
            start = i = i + 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            blank(start, min(i, len(source)), both=False)
            i += 1
        elif char := re.compile(r"'(?:\\.[^']*|[^'\\])'").match(source, i):
            blank(char.start() + 1, char.end() - 1, both=False)
            i = char.end()
        else:
            i += 1
    return "".join(text), "".join(mask)


def balanced(mask, opener):
    closer = {"(": ")", "[": "]"}[mask[opener]]
    depth = 0
    for i in range(opener, len(mask)):
        depth += (mask[i] == mask[opener]) - (mask[i] == closer)
        if not depth:
            return i + 1
    raise ValueError(f"unbalanced {mask[opener]} at offset {opener}")


KANI_ATTRIBUTE = r"#\s*\[\s*(?:cfg_attr\s*\(\s*kani\s*,\s*)?kani\s*::\s*"
MACROS = (
    ("assume", re.compile(r"\bkani\s*::\s*assume\s*\(")),
    ("assume", re.compile(r"\bkani\s*::\s*any_where\s*(?:::\s*<[^<>]*(?:<[^<>]*>[^<>]*)*>\s*)?\(")),
    ("cover", re.compile(r"\bkani\s*::\s*cover\s*!\s*\(")),
    ("stub", re.compile(KANI_ATTRIBUTE + r"stub\s*\(")),
)
PROOF = re.compile(KANI_ATTRIBUTE + r"proof(?:_for_contract\s*\([^)]*\))?\s*\)?\s*\]")
FUNCTION = re.compile(r"(?:pub(?:\s*\([^)]*\))?\s+)?(?:(?:async|unsafe|const)\s+)*fn\s+(\w+)")
KANI_TOKEN = re.compile(r"\bkani\s*::\s*(?:assume|any_where|cover|stub|proof)\w*\b")
RENAMING_IMPORT = re.compile(r"\buse\b[^;]*?\bkani\b[^;]*?(?:\bas\b|\*|\b(?:assume|any_where|cover|stub|proof)\w*\b)|\bextern\s+crate\s+kani\s+as\b")


def kani_surface(path):
    text, mask = rust_masks(path.read_text(encoding="utf-8"))
    if renaming := RENAMING_IMPORT.search(mask):
        raise ValueError(f"{path}: '{collapse(renaming[0])}' brings a Kani assumption, cover, stub or harness attribute in under another name; write each as kani::<name> so the record can read it")
    surface = Surface()
    spans, read = [], []
    for kind, pattern in MACROS:
        for match in pattern.finditer(mask):
            end = balanced(mask, match.end() - 1)
            read.append((match.start(), end))
            spans.append((match.start(), kind, collapse(text[match.end():end - 1])))
    for match in PROOF.finditer(mask):
        read.append(match.span())
        i = match.end()
        while True:
            i = len(mask) - len(mask[i:].lstrip())
            if mask.startswith("#", i):
                i = balanced(mask, mask.index("[", i))
            else:
                break
        name = FUNCTION.match(mask, i)
        if not name:
            raise ValueError(f"{path}: #[kani::proof] at offset {match.start()} is not followed by a function")
        spans.append((match.start(), "harness", name[1]))
    for token in KANI_TOKEN.finditer(mask):
        if not any(start <= token.start() < end for start, end in read):
            line = mask.count("\n", 0, token.start()) + 1
            raise ValueError(f"{path}:{line}: '{collapse(token[0])}' is in a form the record cannot read; write kani::assume(...), kani::any_where(...), kani::cover!(...), #[kani::stub(...)] or #[kani::proof], alone or under #[cfg_attr(kani, ...)]")
    for _, kind, item in sorted(spans):
        surface.add(f"{kind} {item}")
    return surface


SURFACES = {"lean": lean_surface, "tla": tla_surface, "kani": kani_surface}


def digest(surface):
    return hashlib.sha256(json.dumps(surface, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()


def read_record(path):
    record = json.loads(path.read_text(encoding="utf-8"))
    models = record.get("models") if isinstance(record, dict) else None
    if not isinstance(models, dict) or record.get("format") != FORMAT:
        raise ValueError(f"{path}: unsupported record format")
    for model, entry in models.items():
        if not isinstance(entry, dict) or entry.get("kind") not in SURFACES or not isinstance(entry.get("surface"), dict):
            raise ValueError(f"{path}: malformed entry for {model}")
    return models


def write_record(path, models):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(json.dumps({"format": FORMAT, "models": models}, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


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


def differences(kind, old, new):
    lines = []
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
    arguments = parser.parse_args()
    if arguments.command == "record":
        return record(arguments.record_file, arguments.models)
    return compare(arguments.record_file)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL baseline: {error}")
        sys.exit(1)
