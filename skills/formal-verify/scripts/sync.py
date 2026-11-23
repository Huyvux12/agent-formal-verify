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
history, and otherwise the last commit that changed the model files. Each source path is
followed through every rename since the sync commit in both directions. Each name adds the
files where git grep finds it as a whole word now, outside the model files; a Rust model
file is production code, so it stays in the search. Exits 1 outside a git repository.

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
    for model in models:
        found = HEADER.search(model.read_text(encoding="utf-8", errors="replace"))
        if found and git(root, "merge-base", "--is-ancestor", found[1], "HEAD", check=False).returncode == 0:
            return git(root, "rev-parse", found[1]).stdout.strip(), f"from the Source read at line in {model.name}"
    last = git(root, "log", "-1", "--format=%H", "--", *map(str, models)).stdout.strip()
    if last:
        return last, "from the last commit of the model files"
    return None, "the model files have no commit and no Source read at line in HEAD's history"


def renamed(root, sync, paths):
    """Add every path that the renames since sync connect to one of paths."""
    pairs = []
    for line in git(root, "log", "-M", "--diff-filter=R", "--name-status", "--format=", f"{sync}..HEAD").stdout.splitlines():
        fields = line.split("\t")
        if len(fields) == 3 and fields[0].startswith("R"):
            pairs.append((fields[1], fields[2]))
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
    paths = renamed(root, sync, [str((Path.cwd() / source).resolve().relative_to(root)) for source in arguments.source])
    excluded = [f":(exclude){path}" for path in relative if not path.endswith(".rs")]
    missing = []
    for name in arguments.name:
        files = git(root, "grep", "-l", "-w", "-e", name, "--", ".", *excluded, check=False).stdout.splitlines()
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
