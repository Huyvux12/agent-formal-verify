# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Match Lake's queried objects to the library roots in its own Lean search path."""
import os
import sys
from pathlib import Path


def main(objects, modules, libraries):
    roots = sorted({Path(entry).resolve() for entry in os.getenv("LEAN_PATH", "").split(os.pathsep) if entry},
                   key=lambda path: len(path.parts), reverse=True)
    names, owners = [], set()
    for line in objects.read_text(encoding="utf-8").splitlines():
        path = Path(line)
        # The object itself may link into an artifact cache. Its location in the library names the module.
        path = path.parent.resolve() / path.name
        owner = next((root for root in roots if root in path.parents), None)
        if owner is None or path.suffix != ".olean":
            raise ValueError(f"cannot identify the module of {line}")
        names.append(".".join(path.relative_to(owner).with_suffix("").parts))
        owners.add(owner)
    modules.write_text("".join(name + "\n" for name in names), encoding="utf-8")
    libraries.write_text("".join(str(root) + "\n" for root in sorted(owners)), encoding="utf-8")


if __name__ == "__main__":
    try:
        main(*(Path(arg) for arg in sys.argv[1:]))
    except (ValueError, OSError) as error:
        sys.exit(str(error))
