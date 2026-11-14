#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean MassTime/Scales.lean
lake env lean MassTime/Static.lean
