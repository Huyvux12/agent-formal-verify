#!/bin/bash
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
# Shared Python check for the helpers, which need Python 3.9 or later as python3.

require_python() {
  local version
  version=$(python3 -c 'import sys; print("%d.%d.%d" % sys.version_info[:3]); sys.exit(sys.version_info < (3, 9))' 2> /dev/null) && return 0
  if [ -n "$version" ]; then
    echo "UNAVAILABLE python3 is Python $version; install Python 3.9 or later"
  else
    echo "UNAVAILABLE python3 is not on PATH or does not run; install Python 3.9 or later"
  fi
  return 3
}
