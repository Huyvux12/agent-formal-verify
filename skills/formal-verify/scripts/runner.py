# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""What the checker runners share: the unavailable-tool error, time limits, atomic writes and the entry point."""
import os
import re
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
import processes
import storage

LIMIT = re.compile(r"\+?0*([1-9][0-9]{0,9})([smh]?)")
SECONDS = {"": 1, "s": 1, "m": 60, "h": 3600}


class Unavailable(Exception):
    """A tool the check needs is missing, unusable or unverified. The message is the UNAVAILABLE line to print."""


def parse_limit(setting, raw, kind, default):
    """Return a time limit's label with its unit and its length in seconds, or raise Unavailable naming the setting."""
    limit = LIMIT.fullmatch(raw)
    if not limit or int(limit[1]) >= 2**32:
        raise Unavailable(f"UNAVAILABLE {setting}={raw!r} is not a {kind}; set a whole number from 1 to 4294967295 "
                          f"with an optional unit s, m or h, such as 90s or 20m, or unset it for {default}")
    return limit[1] + (limit[2] or "s"), int(limit[1]) * SECONDS[limit[2]]


def atomic_write(path, text):
    """Replace a file's content in one step, so a reader never sees it half written."""
    path = Path(path)
    descriptor, temporary = tempfile.mkstemp(dir=path.parent, prefix=f".{path.name}.")
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(text)
        os.replace(temporary, path)
    finally:
        Path(temporary).unlink(missing_ok=True)


def run(main):
    """Exit with main's status: 1 when TMPDIR is unusable, 3 when a tool is unavailable, or by a handled signal."""
    try:
        with processes.signal_cleanup():
            status = main()
    except storage.TempDirError as error:
        print(error)
        status = 1
    except Unavailable as error:
        print(error)
        status = 3
    except processes.SignalTerminated as error:
        error.exit()
    sys.exit(status)
