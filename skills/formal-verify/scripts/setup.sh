#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Ensures one tool is ready; system runtimes must already be installed.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=skills/formal-verify/scripts/python-tools.sh
source "$HERE/python-tools.sh"

report_storage() {
  if command -v python3 > /dev/null 2>&1; then
    python3 "$HERE/storage.py" report
  fi
}

case ${1:-} in
  tla)
    # shellcheck source=skills/formal-verify/scripts/tlc-tools.sh
    source "$HERE/tlc-tools.sh"
    require_tlc_runtime
    tlc_jar_ready
    echo "READY TLC $TLC_JAR"
    report_storage
    ;;
  rust)
    [ "$#" -eq 1 ] || { echo "usage: setup.sh rust"; exit 2; }
    require_python || exit 3
    python3 "$HERE/kani.py" ready
    report_storage
    ;;
  lean)
    [ "$#" -eq 2 ] || { echo "usage: setup.sh lean <lake-project-dir>"; exit 2; }
    dir=$2
    # shellcheck source=skills/formal-verify/scripts/lean-tools.sh
    source "$HERE/lean-tools.sh"
    toolchain=$(lean_pin "$dir") || { status=$?; echo "$toolchain"; exit "$status"; }
    if ! lean_pin_ready "$toolchain"; then
      install_log=$(elan toolchain install "$toolchain" 2>&1) \
        || { echo "UNAVAILABLE cannot install $toolchain; run elan toolchain install $toolchain"; echo "$install_log"; exit 3; }
      lean_pin_ready "$toolchain" || { echo "UNAVAILABLE $toolchain does not run after installation; check elan toolchain list and reinstall it"; echo "$install_log"; exit 3; }
      [ -z "$install_log" ] || echo "$install_log"
    fi
    echo "READY Lean $toolchain"
    report_storage
    ;;
  storage)
    [ "$#" -eq 1 ] || { echo "usage: setup.sh storage"; exit 2; }
    require_python || exit 3
    python3 "$HERE/storage.py" report
    ;;
  *) echo "usage: setup.sh tla | setup.sh lean <lake-project-dir> | setup.sh rust | setup.sh storage"; exit 2 ;;
esac
