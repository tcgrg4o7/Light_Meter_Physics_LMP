# Manuscript 9: mass as a time

Checked Lean companion for gravitational time, radius light-time, the Newtonian
Schuler scales and the exact Schwarzschild static-clock gradient. The project
uses `MassTime` as its namespace and `mass_time` as its package name.

## Source, versions and verification

- [Pinned manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/52f63595611ddfb987076dad328fef24735bb45d/papers/09-mass-as-a-time/9.%20mass%20as%20a%20time.tex).
- Source commit: `52f63595611ddfb987076dad328fef24735bb45d`.
- Source SHA-256: `8f9bf644a443f29556a4838572e2f5a0a42eb028e99ebdb91c54bb1e68fabe94`.
- Lean 4.19.0; mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Dependency revisions are locked in `lake-manifest.json`.

The root imports both proof modules. The 30 named statements passed the project
build and direct Lean checking on 2026-11-14. All axiom reports list only
`propext`, `Classical.choice`, and `Quot.sound`, with no unfinished proofs or
custom axioms. These are conditional mathematical results, not validation of
physical interpretations or observations.

## Model inputs and domains

`Parameters.mu` means the positive gravitational parameter `GM`, not mass alone.
`Parameters.c` is positive. The code uses real numbers in a consistent unit
system, not dimensionally typed quantities.

The scales are defined as in the manuscript:

| Code | Manuscript meaning |
|---|---|
| `gravitationalTime` | `tau_g = GM/c³` |
| `radiusTime R` | `t_R = R/c` |
| `schwarzschildRadius` | `r_s = 2GM/c²` |
| `compactness R` | `x_R = GM/(R c²)` |
| `newtonianGravity R` | `g_N = GM/R²` |
| `gravityInverseTime R` | `f_g = g_N/c`, an inverse-time scale, **not cyclic frequency** |
| `schulerOmega R` | Positive square root of `GM/R³`, the Newtonian angular-frequency scale |
| `schulerTime R` | `tau_S = 1/omega_S`, the one-radian timescale |
| `schulerFrequency R` | `f_S = omega_S/(2 pi)`, cyclic frequency |
| `schulerPeriod R` | `T_S = 2 pi/omega_S`, the full period |

No `tau_a = c/g_N` quantity is introduced. No factor of `2 pi` is inserted into
`f_g`. Gravitational time and radius light-time are scales, not clock periods or
claims about a signal trajectory. The Newtonian Schuler law is a model input;
the navigation-error dynamics are not derived from relativistic clock rates.

Scale results use `R>0`. Static-clock and derivative results additionally use
`R>r_s`, with the Schwarzschild lapse `alpha=sqrt(1-r_s/R)`. Physically this must
also be an areal radius in the vacuum exterior outside the source, for a static
observer with time normalized at infinity. The code does not model a source
boundary, prove the Einstein equations or establish that a real body satisfies
these idealizations. The horizon equality is only an algebraic boundary relation;
it is not an admissible static observer.

## Checked statements and source mapping

### `MassTime/Scales.lean` (16 statements)

| Source | Checked content |
|---|---|
| `eq:mass-time`, `eq:radius-time` | Positive gravitational time and radius light-time |
| `eq:schwarzschild-radius` | `r_s = 2 c tau_g` |
| `eq:compactness`, `eq:three-scales-depth` | `x_R = tau_g/t_R` |
| `eq:three-scales-fg` | `tau_g/t_R² = f_g = omega_S² t_R` |
| `eq:schuler-kepler`, `eq:schuler-mode` | Positive square-root branch, `omega_S² = GM/R³ = g_N/R` |
| `eq:three-scales-schuler` | `omega_S² = tau_g/t_R³` |
| `eq:three-time-law` | `t_R³ = tau_g tau_S²` |
| `eq:log-position` | `ln(t_R/tau_g) = (2/3) ln(tau_S/tau_g)`, with positivity supplying logarithm domains |
| `eq:schuler-times` | Positive `tau_S`, `T_S = 2 pi tau_S`, `f_S T_S = 1` |
| `eq:lag`, `eq:mass-time-lag` | Within the explicitly named first-order lag model, its value at `dt=t_R` is `tau_g` |

### `MassTime/Static.lean` (14 statements)

- `exterior_radicand_pos`, `lapse_pos`, `inverse_rate_pos` establish the
  positive branch and admissible division/logarithm domains.
- `radius_ratio_compactness`, `exact_inverse_rate`, `exact_inverse_excess`
  verify `r_s/R=2x_R`, `delta=1/sqrt(1-2tau_g/t_R)`, and
  `epsilon=1/sqrt(1-2x_R)-1` (`eq:inverse-rate`, `eq:exact-rate`).
- `horizon_time_equivalence` checks `R=r_s` iff `t_R=2tau_g`.
- `weak_excess_first_derivative` proves the derivative of
  `1/sqrt(1-2x)-1` at zero is one, checking the first-order coefficient in
  `eq:weak-rate` without asserting a finite approximation error.
- `radial_radicand_derivative`, `inverse_rate_derivative`, and
  `log_inverse_rate_derivative` formally differentiate the radial functions.
- `exact_proper_gradient` proves the outward radial coefficient
  `c² alpha * d(log delta)/dr = -GM/(r² alpha)` (`eq:proper-gradient`,
  `eq:exact-gradient`).
- `exact_proper_gradient_inward` proves this coefficient is strictly negative.
- `proper_gradient_inverse_time` proves its negative divided by `c` is exactly
  `f_g/alpha`, retaining the lapse correction.

## Exact gradient versus weak-field approximation

`properRadialGradient F r` is defined as `alpha(r) * deriv F r`, encoding the
manuscript's spatial-metric input `dL=dr/alpha`. It is **not** the coordinate
derivative alone. This is a scalar coefficient in the outward radial direction;
a full vector field or differential-geometric gradient is not formalized.
The result has the sign and coefficient of the manuscript's formula, but the
identification with the acceleration of a static worldline is not independently
derived from connection coefficients here.

The exact inverse-time magnitude is `f_g/alpha`. Replacing it with `f_g` uses
the weak-field approximation `alpha≈1`; the code does not erase that factor.
Likewise `epsilon≈x_R` and the lag formula are not exact Schwarzschild identities.
`firstOrderLag R dt := x_R*dt` is explicitly an approximation-model definition.
Its algebraic equality at `dt=t_R` does not prove the exact accumulated lag equals
`tau_g`. The derivative-at-zero result is not a remainder bound for a chosen
finite compactness.

## Reproduce

Install [Elan/Lean](https://lean-lang.org/install/) and put `lake` on PATH. From
the repository root:

```bash
cd papers/09-mass-as-a-time/lean
bash check.sh
```

Lake restores the pinned dependencies; first-time setup needs network access and
may compile missing mathlib modules. Precompiled caches are optional. Do not run
`lake update` merely to reproduce this snapshot. The script uses the caller's
installation, builds the root and directly checks both modules, printing all
30 axiom reports. No GitHub Actions run is implied by the local checks.

Lean division is total, even at zero; helper identities outside physical domains
do not authorize a physical interpretation there. `noncomputable` real-number
definitions do not bypass proof checking or create numerical approximations.

## Not covered

No numerical certification of the Earth/Sun tables, measurement uncertainties,
geodetic clock-transfer model, higher-order Taylor coefficients or remainder
bounds, oscillator ODE solution, Einstein-field-equation derivation, or causal
link between navigation and gravity. No new field, density, physical oscillation
or material clock deficit is inferred from these identities.
