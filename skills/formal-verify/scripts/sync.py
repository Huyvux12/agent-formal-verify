#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""List the commits an existing model has not been synced with, and the paths its covered code has had since.

  SYNC <commit> <reason>     the commit the model was last synced at, or SYNC none
  PATH <path>                a path the covered code has had since that commit
  MISSING <name>: <commits>  a covered name that git grep finds in no file that could define it,
                             with the commits since the sync that added or removed it
  READ <command>             the git log command that shows every commit to read

The sync commit is the header's `Source read at <commit>` when that commit is in HEAD's
history, and otherwise the last commit that changed the model files; the SYNC line then says
why the header's commit was not used. When a model file is also a --source, such as a Rust file
with its Kani harness, that fallback counts only a commit that changed the code of its
#[cfg(kani)] items, or another model file, and none of its other code; SYNC none follows when
none of the last 100 commits of the model files since the source's last rename qualifies. Each source path is followed through every rename since
the sync commit in both directions. Each name adds the files where git grep finds it as a whole
word now, outside the model files that are not also a --source, such as a Kani harness kept
apart from the production code, and outside documents and TLA+ and Lean files, which cannot
define it, unless a source path has the same extension. A name in none of the remaining files
is MISSING. Each name also adds, under the same rules, the files where a commit since the sync
added or removed it as a whole word, which git log -S finds, renames included. A path that held
the code only under another name, such as code renamed as it moved, is not found, nor is one
whose commits all kept the number of times the name appears. Exits 1 outside a git
repository, for a source path that no commit has, or when git grep fails.

Usage: sync.py <model file>... [--source <path>]... [--name <name>]...
"""
import argparse
import functools
import re
import shlex
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True
import baseline

HEADER = re.compile(r"Source read at ([0-9a-fA-F]{7,40})\b")
# Documents and model files mention covered names but cannot define them, unless a source has the same extension.
NO_DEFINITIONS = {".md", ".markdown", ".rst", ".txt", ".adoc", ".org", ".tla", ".cfg", ".lean", ".statements", ".matrix", ".mutations"}
# #[cfg(kani)] on an item, past any other attributes and its visibility; on a field or a variant it is production code.
KANI_CFG = re.compile(
    r"#\s*\[\s*cfg\s*\(\s*kani\s*\)\s*\](?=(?:\s*#\s*\[[^\]]*\])*\s*(?:pub\s*(?:\([^)]*\))?\s*)?"
    r"(?:mod|fn|impl|use|const|static|struct|enum|union|trait|type|unsafe|extern|async|macro_rules)\b)"
)
# The fallback reads at most this many commits of the model files, since each costs a parse of the file twice.
FALLBACK_COMMITS = 100


def git(root, *arguments, check=True):
    done = subprocess.run(["git", "-C", str(root), *arguments], capture_output=True, text=True, check=False)
    if check and done.returncode:
        raise RuntimeError(f"git {' '.join(arguments)} failed: {done.stderr.strip()}")
    return done


@functools.cache
def split_harness(text):
    """Return the code of the #[cfg(kani)] items in Rust text and the code outside them, without comments or blank lines."""
    source = baseline.rust_masks(text)
    mask, spans = source.without_comments_or_strings, []
    for found in KANI_CFG.finditer(mask):
        if spans and found.start() < spans[-1][1]:
            continue
        at = found.end()
        while at < len(mask) and mask[at] not in "{;":
            at = baseline.after_closing(mask, at) if mask[at] in "([" else at + 1
        end = baseline.after_closing(mask, at) if at < len(mask) and mask[at] == "{" else at + 1
        spans.append((found.start(), end))
    starts = [0] + [end for _, end in spans]
    ends = [start for start, _ in spans] + [len(mask)]

    def code(parts):
        return [line.rstrip() for part in parts for line in part.splitlines() if line.strip()]

    return code(source.uncommented[a:b] for a, b in spans), code(source.uncommented[a:b] for a, b in zip(starts, ends))


def changed_only_harness(root, commit, models, sources):
    """Whether commit changed the model files and, in those that are also a source, no code outside the #[cfg(kani)] items.

    Returns the path instead when commit renamed a source to it, since git log does not follow the rename.
    """
    touched = set(git(root, "diff-tree", "--root", "--no-commit-id", "--name-only", "-r", "-z", commit, "--", *models).stdout.split("\0")) - {""}
    changed = bool(touched - set(sources))
    for path in touched & set(sources):
        before, after = (git(root, "show", f"{revision}:{path}", check=False) for revision in (f"{commit}^", commit))
        if before.returncode or after.returncode:
            renames = git(root, "diff-tree", "-M", "-r", "--no-commit-id", "--name-only", "--diff-filter=R", "-z", commit).stdout.split("\0")
            return path if path in renames else False
        try:
            (old_harness, old_code), (new_harness, new_code) = split_harness(before.stdout), split_harness(after.stdout)
        except ValueError:
            return False
        if old_code != new_code:
            return False
        changed = changed or old_harness != new_harness
    return changed


def sync_commit(root, models, shared):
    """Return the sync commit and where it came from, or (None, reason); shared are the models also given as --source."""
    unused = []
    for model in models:
        text = model.read_text(encoding="utf-8", errors="replace")
        found = HEADER.search(text)
        if found and git(root, "merge-base", "--is-ancestor", found[1], "HEAD", check=False).returncode == 0:
            return git(root, "rev-parse", found[1]).stdout.strip(), f"from the Source read at line in {model.name}"
        if found:
            unused.append(f"the Source read at commit {found[1]} in {model.name} is not in HEAD's history")
        elif "Source read at" in text:
            unused.append(f"the Source read at line in {model.name} names no commit hash")
    relative = [str(model.relative_to(root)) for model in models]
    if shared:
        names = ", ".join(model.name for model in shared)
        sources = [str(model.relative_to(root)) for model in shared]
        commits = git(root, "log", f"-{FALLBACK_COMMITS + 1}", "--format=%H", "--", *relative).stdout.split()
        read = "the model files"
        if len(commits) > FALLBACK_COMMITS:
            commits, read = commits[:FALLBACK_COMMITS], f"the last {FALLBACK_COMMITS} commits of the model files"
        since = ""
        for commit in commits:
            found = changed_only_harness(root, commit, relative, sources)
            if isinstance(found, str):
                since = f" since the rename to {Path(found).name} in {commit}, which git log does not follow"
                break
            if found:
                return commit, "; ".join([f"from the last commit of the model files that changed no production code in {names}", *unused])
        return None, "; ".join([f"no commit of {read} changed only the #[cfg(kani)] items of {names}{since}", *unused])
    last = git(root, "log", "-1", "--format=%H", "--", *relative).stdout.strip()
    if last:
        return last, "; ".join(["from the last commit of the model files", *unused])
    return None, "; ".join(["the model files have no commit and no Source read at line in HEAD's history", *unused])


def renamed(root, sync, paths):
    """Add every path that the renames since sync connect to one of paths."""
    fields = git(root, "log", "-M", "--diff-filter=R", "--name-status", "--format=", "-z", f"{sync}..HEAD").stdout.split("\0")
    fields = [field.lstrip("\n") for field in fields]
    pairs = [(fields[at + 1], fields[at + 2]) for at in range(len(fields) - 2) if re.fullmatch(r"R[0-9]*", fields[at])]
    paths = set(paths)
    grown = True
    while grown:
        grown = False
        for old, new in pairs:
            if (old in paths) != (new in paths):
                paths |= {old, new}
                grown = True
    return paths


def held(root, sync, name, pathspec):
    """Return the files where a commit since sync added or removed name as a whole word."""
    # One log lists each such commit, its parents and the files where the raw count of name changed, and a few greps
    # read those files at each commit and its first parent. Without --no-renames, a rename that keeps the name's
    # count pairs the old path with the new one and -S skips both. A path holds no NUL, so the two NULs before each
    # header mark it, and -z puts one newline before the header's first path.
    log = git(root, "log", "--no-renames", "--no-textconv", "-S", name, "--format=%x00%x00%H %P", "--name-only", "-z",
              f"{sync}..HEAD", "--", *pathspec).stdout
    changed = {}
    for entry in re.split("\0\0+", log)[1:]:
        header, _, names = entry.partition("\0")
        commit, *parents = header.split()
        # A root commit, such as one of a history merged in, changed nothing since the sync.
        for revision in (commit, parents[0]) if parents else ():
            changed.setdefault(revision, set()).update(file for file in names.removeprefix("\n").split("\0") if file)
    files = set()
    for revisions in batches(changed):
        paths = sorted(set().union(*(changed[revision] for revision in revisions)))
        found = git(root, "grep", "-l", "-z", "-w", "-F", "-e", name, *revisions, "--", *(f":(literal){path}" for path in paths), check=False)
        if found.returncode > 1:
            raise RuntimeError(f"git grep for {name} failed: {found.stderr.strip()}")
        hits = (hit.partition(":") for hit in found.stdout.split("\0") if hit)
        files.update(file for revision, _, file in hits if file in changed[revision])
    return files


def batches(changed, limit=100_000):
    """Split the revisions of changed into groups whose revisions and paths stay within limit bytes of arguments."""
    group, paths, size = [], set(), 0
    for revision, files in changed.items():
        grown = sum(len(path.encode()) + 12 for path in files - paths) + len(revision) + 1
        if group and size + grown > limit:
            yield group
            group, paths, size = [], set(), 0
            grown = sum(len(path.encode()) + 12 for path in files) + len(revision) + 1
        group.append(revision)
        paths |= files
        size += grown
    if group:
        yield group


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("models", nargs="+", type=Path)
    parser.add_argument("--source", action="append", default=[], help="a source file the model's header names")
    parser.add_argument("--name", action="append", default=[], help="a function or shared variable the model covers")
    arguments = parser.parse_args()
    models = [model.resolve() for model in arguments.models]
    for model in models:
        if not model.is_file():
            print(f"FAIL {model} does not exist")
            return 1
    found = git(models[0].parent, "rev-parse", "--show-toplevel", check=False)
    if found.returncode:
        print(f"FAIL {models[0]} is in no git repository")
        return 1
    root = Path(found.stdout.strip())
    relative = [str(model.relative_to(root)) for model in models]
    given = {(Path.cwd() / source).resolve() for source in arguments.source}
    sync, reason = sync_commit(root, models, [model for model in models if model in given])
    if sync is None:
        print(f"SYNC none: {reason}; compare the model with the code in full")
        return 0
    print(f"SYNC {sync} {reason}")
    sources = []
    for source in arguments.source:
        path = (Path.cwd() / source).resolve()
        if root not in path.parents or not git(root, "log", "-1", "--format=%H", "--", str(path.relative_to(root))).stdout:
            print(f"FAIL --source {source} is {path}, which no commit in {root} has")
            return 1
        sources.append(str(path.relative_to(root)))
    paths = renamed(root, sync, sources)
    excluded = [f":(exclude){path}" for path in relative if path not in sources]
    cannot_define = NO_DEFINITIONS - {Path(path).suffix.lower() for path in paths}
    missing = []
    for name in arguments.name:
        found = git(root, "grep", "-l", "-z", "-w", "-F", "-e", name, "--", ".", *excluded, check=False)
        if found.returncode > 1:
            raise RuntimeError(f"git grep for {name} failed: {found.stderr.strip()}")
        files = [file for file in found.stdout.split("\0") if file and (file in paths or Path(file).suffix.lower() not in cannot_define)]
        if not files:
            missing.append(name)
        files += held(root, sync, name, [".", *excluded])
        paths.update(file for file in files if file in paths or Path(file).suffix.lower() not in cannot_define)
    for path in sorted(paths):
        print(f"PATH {path}")
    for name in missing:
        removed = git(root, "log", "-S", name, "--format=%h", f"{sync}..HEAD", "--", *sorted(paths)).stdout.split()
        print(f"MISSING {name}: " + (" ".join(removed) if removed else "no commit since the sync removed it"))
    if paths:
        print("READ " + shlex.join(["git", "-C", str(root), "log", "-p", f"{sync}..HEAD", "--", *sorted(paths)]))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (RuntimeError, ValueError) as error:
        print(f"FAIL {error}")
        sys.exit(1)
