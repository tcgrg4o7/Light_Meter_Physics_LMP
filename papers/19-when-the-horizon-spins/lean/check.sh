#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean Kerr/Roots.lean
lake env lean Kerr/Thermodynamics.lean
lake env lean Kerr/Extraction.lean
