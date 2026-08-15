#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
# Adapted from Tau Ceti's docbuild at commit e51dd9b19fdd; modified for Connes.
"""Generate the private doc-gen4 root importing every Connes module."""

from pathlib import Path


HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "Connes"
OUTPUT = HERE / "ConnesDocs.lean"


def main() -> None:
    modules = sorted(
        ".".join(path.relative_to(SOURCE.parent).with_suffix("").parts)
        for path in SOURCE.rglob("*.lean")
    )
    OUTPUT.write_text("\n".join(f"import {module}" for module in modules) + "\n")
    print(f"wrote {OUTPUT} importing {len(modules)} modules")


if __name__ == "__main__":
    main()
