# Manuscript 4 Lean pilot: checked algebra and worldline phase

Status: **compiled successfully on 2026-11-14** using Lean 4.19.0.
The thirteen statements in the two modules passed `lake build` and direct Lean checking.
Their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
no unfinished proof or custom axiom is used. This validates the listed formal
algebraic statements, not the entire paper or its empirical interpretations.

## Reproducibility

- Manuscript commit: `0e76801d08ad946949e150299e32020330dd660c`.
- Source path: `papers/04-compton-frequency/4. compton_frequency.tex`.
- [Pinned manuscript source](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/0e76801d08ad946949e150299e32020330dd660c/papers/04-compton-frequency/4.%20compton_frequency.tex).
- Source SHA-256: `b62cd1117dda297130973a7f41cb8d0db340b9c2fa6eabac5d6cfd0870f15e45`.
  The manuscript is not duplicated in this proof folder.
- Compatible release pair: Lean 4.19.0 / mathlib v4.19.0.
  The official mathlib release's `lean-toolchain` was checked.
- mathlib release tag resolves to `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
  The generated `lake-manifest.json` locks it and its dependencies.

## Source-to-theorem ledger

| Source equation | Checked theorem | Coverage / conditions |
|---|---|---|
| `eq:gamma-frequency` | `energyFrequency_eq_gamma_mul_comptonFrequency` | Exact scalar algebra given E = gamma m c² |
| `eq:kinetic-frequency` | `kineticFrequency_eq_difference` | Definition and subtraction |
| `eq:kinetic-frequency` | `kineticFrequency_eq_gamma_sub_one` | Given the same energy relation |
| `eq:path-phase-rate` | `pathFrequency_eq_compton_div_gamma` | Algebraic middle equality only; 1D, nonzero gamma, E = gamma m c², p = gamma m v, gamma²(c²-v²)=c² |
| `eq:plane-wave`, `eq:path-phase-rate` | `phaseCycles_along_inertial_path` | Affine phase identity in cycles; x=x₀+vt |

All checked statements are universally quantified over real scalars. The
energy identities need no positivity for algebra, but their physical use requires
m,c,h > 0. Lean division is total at zero, so algebra without nonzero hypotheses
must not be mistaken for permitting zero Planck constant physically. In particular,
`energyFrequency_eq_gamma_mul_comptonFrequency` remains algebraically true at
`h=0` because Lean defines division by zero to be zero; physical frequency
requires a positive Planck constant `h>0`.

## Worldline extension: now checked

`ComptonPilot/Worldline.lean` adds eight checked statements, including supporting
lemmas. Gamma is defined as `1 / sqrt(1 - v²/c²)`, not supplied as an arbitrary
number satisfying an assumed normalization. With `c > 0` and `|v| < c`, Lean proves:

- `subluminal_gap`: `c²-v² > 0`.
- `gamma_radicand_pos`: the square-root argument is positive.
- `lorentzGamma_pos`: gamma is positive.
- `lorentzGamma_normalization`: `gamma²(c²-v²)=c²`.
- `pathFrequency_from_subluminal`: `(E-pv)/h = νC/gamma`, assuming
  `E=gamma*m*c²` and `p=gamma*m*v`.
- `energy_minus_momentum_velocity_pos`: `E-pv > 0`, additionally assuming `m>0`.
- `phaseCycles_hasDerivAt`: the derivative of
  `(p*(x₀+v*t)-E*t)/h` is `(pv-E)/h` for constant parameters.
- `abs_phaseCycles_deriv`: its absolute derivative is `νC/gamma`, additionally
  assuming `h>0` and positive mass.

Source mapping: the gamma definition and energy/momentum hypotheses are from
`eq:energy-momentum`; the affine path and signed phase follow `eq:plane-wave`;
the derivative and absolute-rate result cover the one-dimensional cycle-form
version of `eq:path-phase-rate`. This improves the initial algebra theorem:
its normalization assumption is now discharged by a separate theorem.

## Still outside checked coverage

- A formal radians-to-cycles bridge with `h = 2*pi*hbar`. Current phase functions
  are expressed directly in cycles using `/h`, rather than radians using `/hbar`.
- A defined proper-time function and the final `νC * dτ/dt` equality.
- Three-dimensional vector generalization, acceleration or curved spacetime.
- Gravitational approximations, numerical physical constants, experiment and
  interpretation. No radiating Compton oscillator is claimed.

## Reproduce and inspect

Install [Elan/Lean using the official instructions](https://lean-lang.org/install/)
and ensure `lake` is on your PATH. Elan selects the version in `lean-toolchain`.
From the repository root:

```bash
cd papers/04-compton-frequency/lean
lake exe cache get Mathlib/Data/Real/Sqrt.lean Mathlib/Analysis/Calculus/Deriv/Add.lean Mathlib/Analysis/Calculus/Deriv/Mul.lean Mathlib/Tactic/FieldSimp.lean Mathlib/Tactic/Linarith.lean
bash check.sh
```

The cache command is optional: `bash check.sh` can compile required dependencies
from source, which takes longer on the first run. Lake restores dependencies at
the revisions in `lake-manifest.json`; do not run `lake update` merely to check
this pinned snapshot. A fresh environment needs network access to download Lean
and dependencies. After setup, the proof checks themselves run locally.

`check.sh` runs `lake build` and directly checks both proof modules, printing all
thirteen axiom reports. A successful check exits zero. The expected reports list
only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
axioms. The first build and direct checks passed on 2026-11-14; this folder does
not imply that a GitHub Actions workflow has been installed or has run.

Review the mathematical hypotheses and source fidelity in addition to building.
The initial algebraic path theorem has an explicit normalization hypothesis;
the new physical specialization derives it from the square-root definition.

`noncomputable def` marks real-number division definitions that cannot be emitted
as executable numerical code. It does not skip proof checking.
