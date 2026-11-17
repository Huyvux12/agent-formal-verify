# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Read a frozen Lean statements record."""
import json


def read_record(path):
    record = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(record, dict) or record.get("format") != 1:
        raise ValueError(f"{path}: unsupported statements format")
    if not isinstance(record.get("toolchain"), str) or not isinstance(record.get("module"), str):
        raise TypeError(f"{path}: missing toolchain or module")
    entries = record.get("declarations")
    if not isinstance(entries, list) or not entries:
        raise ValueError(f"{path}: missing declarations")
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict) or not all(isinstance(entry.get(key), str) for key in ("name", "kind", "type", "typeHash")):
            raise ValueError(f"{path}: malformed declaration")
        if "valueHash" not in entry or entry["valueHash"] is not None and not isinstance(entry["valueHash"], str):
            raise ValueError(f"{path}: malformed value hash")
        if entry["name"] in seen:
            raise ValueError(f"{path}: duplicate declaration {entry['name']}")
        seen.add(entry["name"])
    return record
