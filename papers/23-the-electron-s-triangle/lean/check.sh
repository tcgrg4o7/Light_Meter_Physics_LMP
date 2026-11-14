#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake build
lake env lean ElectronTriangle/Kinematics.lean
lake env lean ElectronTriangle/Phase.lean
lake env lean ElectronTriangle/PlaneWave.lean
