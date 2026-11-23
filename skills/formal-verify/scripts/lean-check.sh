#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Builds and audits a Lean 4 model with Lake; lean.py describes the checks.
#
# Usage: lean-check.sh <lake-project-dir> [--freeze] [<file.lean> ...]
#   A file is absolute or relative to the project.
set -euo pipefail
[ "$#" -gt 0 ] || { echo "usage: lean-check.sh <lake-project-dir> [--freeze] [<file.lean> ...]"; exit 2; }
HERE=$(cd "$(dirname "$0")" && pwd)
# shellcheck source=skills/formal-verify/scripts/python-tools.sh
source "$HERE/python-tools.sh"
require_python || exit 3
exec python3 "$HERE/lean.py" check "$@"
