#!/usr/bin/env python3
"""Share only identical pinned dependency packages, never project build outputs.
Optional CI optimization; ordinary local users can run each project's cache get.
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
projects = [root / line for line in (root / "scripts/lean-projects.txt").read_text().splitlines()
            if line and not line.startswith("#")]
if not projects:
    raise SystemExit("No projects registered")
found = set((root / "papers").glob("*/lean/lakefile.toml"))
if found != {p / "lakefile.toml" for p in projects}:
    raise SystemExit("Companion registry does not match repository projects")
base = projects[0]
packages = json.loads((base / "lake-manifest.json").read_text())["packages"]
toolchain = (base / "lean-toolchain").read_text()
for project in projects:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    if manifest["packages"] != packages or (project / "lean-toolchain").read_text() != toolchain:
        raise SystemExit(f"Different dependency pins in {project}; use separate caches before extending CI")
    if manifest["packagesDir"] != ".lake/packages":
        raise SystemExit(f"Unsupported package directory in {project}")
shared = root / ".lean-cache/packages"
shared.mkdir(parents=True, exist_ok=True)
for project in projects:
    local = project / ".lake/packages"
    local.parent.mkdir(exist_ok=True)
    if local.is_symlink() and local.resolve() == shared.resolve():
        continue
    if local.exists() or local.is_symlink():
        raise SystemExit(f"Refusing to replace existing dependency directory: {local}")
    local.symlink_to(shared, target_is_directory=True)
print("Identical dependency pins verified; shared package cache prepared for", len(projects), "projects")
