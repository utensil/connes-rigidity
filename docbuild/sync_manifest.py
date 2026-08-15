#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Adapted from Tau Ceti's docbuild at commit e51dd9b19fdd; modified for Connes.
"""Synchronize the root project's locked dependencies into the docs project."""

from __future__ import annotations

import json
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT_MANIFEST = HERE.parent / "lake-manifest.json"
DOCS_MANIFEST = HERE / "lake-manifest.json"


def packages_by_name(manifest: dict, path: Path) -> dict[str, dict]:
    packages = manifest["packages"]
    indexed = {package["name"]: package for package in packages}
    if len(indexed) != len(packages):
        raise SystemExit(f"{path} contains duplicate package names")
    return indexed


root = json.loads(ROOT_MANIFEST.read_text())
docs = json.loads(DOCS_MANIFEST.read_text())
root_packages = packages_by_name(root, ROOT_MANIFEST)
packages_by_name(docs, DOCS_MANIFEST)

merged = []
copied = set()
for package in docs["packages"]:
    name = package["name"]
    if name not in root_packages:
        merged.append(package)
        continue
    inherited = dict(root_packages[name])
    inherited["inherited"] = True
    merged.append(inherited)
    copied.add(name)

for package in root["packages"]:
    name = package["name"]
    if name in copied:
        continue
    inherited = dict(package)
    inherited["inherited"] = True
    merged.append(inherited)
    copied.add(name)

missing = set(root_packages) - copied
if missing:
    raise SystemExit(f"failed to synchronize packages: {', '.join(sorted(missing))}")

docs["packages"] = merged
DOCS_MANIFEST.write_text(json.dumps(docs, ensure_ascii=False, indent=1) + "\n")
print(f"synchronized {len(copied)} root dependency pins")
