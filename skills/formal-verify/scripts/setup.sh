#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Ensures one tool is ready; system runtimes must already be installed.
# Each Python readiness check replaces this shell through exec, so a signal sent to this process reaches the check,
# which stops its probe and ends by the signal. A shell waiting for the check would hold the signal until it ended.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=skills/formal-verify/scripts/python-tools.sh
source "$HERE/python-tools.sh"

case ${1:-} in
  tla)
    require_python || exit 3
    exec python3 "$HERE/tlc.py" ready
    ;;
  rust)
    [ "$#" -eq 1 ] || { echo "usage: setup.sh rust"; exit 2; }
    require_python || exit 3
    exec python3 "$HERE/kani.py" ready
    ;;
  lean)
    [ "$#" -eq 2 ] || { echo "usage: setup.sh lean <lake-project-dir>"; exit 2; }
    require_python || exit 3
    exec python3 "$HERE/lean.py" ready "$2"
    ;;
  storage)
    [ "$#" -eq 1 ] || { echo "usage: setup.sh storage"; exit 2; }
    require_python || exit 3
    python3 "$HERE/storage.py" report
    ;;
  *) echo "usage: setup.sh tla | setup.sh lean <lake-project-dir> | setup.sh rust | setup.sh storage"; exit 2 ;;
esac
