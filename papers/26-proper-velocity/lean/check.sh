#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean ProperVelocity/Algebra.lean

lake env lean ProperVelocity/Calculus.lean
lake env lean ProperVelocity/Examples.lean
