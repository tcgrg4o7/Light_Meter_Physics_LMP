#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Use Lean/Lake from the caller's environment. Elan selects lean-toolchain.
lake build
lake env lean ComptonPilot/Exact.lean
lake env lean ComptonPilot/Worldline.lean
