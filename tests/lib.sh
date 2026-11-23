#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Helpers that the shell harnesses source after setting ROOT.

# Runs a check that must fail as a failed check does: with exit 1, not 0, a usage error (2) or a missing tool (3).
# Prints the check's output. On another status, prints the output and the caller's line to stderr and exits 1,
# so the reason shows when the caller redirects the output to a file.
rejected() {
  local out status=0
  out=$("$@") || status=$?
  if [ "$status" -ne 1 ]; then
    printf '%s\n' "$out" >&2
    echo "FAIL ${BASH_SOURCE[1]##*/}:${BASH_LINENO[0]}: a check that must fail exited $status, not 1: $*" >&2
    exit 1
  fi
  printf '%s\n' "$out"
}

# Makes an empty Lake project with the Lean template's settings and its Model directory.
lean_project() {
  mkdir -p "$1/Model"
  cp "$ROOT/skills/formal-verify/examples/lean-template"/{lakefile.toml,lake-manifest.json,lean-toolchain} "$1/"
}
