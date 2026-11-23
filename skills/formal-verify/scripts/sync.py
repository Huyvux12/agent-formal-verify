#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""List the commits an existing model has not been synced with, and every path its covered code has had since.

  SYNC <commit> <reason>     the commit the model was last synced at, or SYNC none
  PATH <path>                a path the covered code has had since that commit
  MISSING <name>: <commits>  a covered name that git grep finds nowhere, with the commits
                             since the sync that removed it
  READ <command>             the git log command that shows every commit to read

The sync commit is the header's `Source read at <commit>` when that commit is in HEAD's
history, and otherwise the last commit that changed the model files; the SYNC line then says
why the header's commit was not used. Each source path is followed through every rename since
the sync commit in both directions. Each name adds the files where git grep finds it as a whole
word now, outside the model files that are not also a --source, such as a Kani harness kept
apart from the production code. Exits 1 outside a git repository, for a source path that no
commit has, or when git grep fails.

Usage: sync.py <model file>... [--source <path>]... [--name <name>]...
"""
import argparse
import re
import shlex
import subprocess
import sys
from pathlib import Path

sys.dont_write_bytecode = True

HEADER = re.compile(r"Source read at ([0-9a-fA-F]{7,40})\b")


def git(root, *arguments, check=True):
    done = subprocess.run(["git", "-C", str(root), *arguments], capture_output=True, text=True, check=False)
    if check and done.returncode:
        raise RuntimeError(f"git {' '.join(arguments)} failed: {done.stderr.strip()}")
    return done


def sync_commit(root, models):
    """Return the sync commit and where it came from, or (None, reason)."""
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
    last = git(root, "log", "-1", "--format=%H", "--", *map(str, models)).stdout.strip()
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
    sync, reason = sync_commit(root, models)
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
    missing = []
    for name in arguments.name:
        found = git(root, "grep", "-l", "-z", "-w", "-F", "-e", name, "--", ".", *excluded, check=False)
        if found.returncode > 1:
            raise RuntimeError(f"git grep for {name} failed: {found.stderr.strip()}")
        files = [file for file in found.stdout.split("\0") if file]
        paths.update(files)
        if not files:
            missing.append(name)
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
