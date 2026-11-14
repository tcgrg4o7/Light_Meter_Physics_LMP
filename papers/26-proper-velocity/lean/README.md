# Manuscript 26: Proper Velocity — Lean companion

This companion proves the general signed one-dimensional relation between proper velocity and coordinate velocity, including both inverse identities and the strict light-speed bound. It also checks the actual chain rule, the longitudinal force derivative, and exact arithmetic for the manuscript's idealized example.

## Reproduce

Install Lean through the official [Lean installation instructions](https://lean-lang.org/install/). From this directory:

```bash
lake exe cache get
bash check.sh
```

For an already provisioned checkout, `bash check.sh` suffices. Lean is pinned to 4.19.0; mathlib is pinned to v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with its transitive dependencies recorded in `lake-manifest.json`. Keep the manifest; dependency updates are intentional changes, not part of the routine check. Initial dependency downloads need internet access and several GB of storage.

The script builds the library and directly rechecks each module, printing axiom dependencies for all 28 named theorems, including supporting lemmas. All were checked using only the standard `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms or unfinished proofs are used. Build and direct checks were also run from the intended repository subfolder using existing cached dependencies. This is not a clean-machine installation test or a claim about hosted CI. No machine-specific paths, tooling, generated outputs, or logs are committed.

## Source and model

Source: [manuscript 26 at commit e71c065](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/e71c06509bc5f1496171f3f6e253c6de76b19f42/papers/26-proper-velocity/26-proper-velocity.tex).

Source SHA-256: `20098b6ad0ea27f9a70872e9523be24cc98aab0b3b2bffaa7bef82de49512022`.

This is flat-spacetime, one-dimensional, massive-particle special-relativistic kinematics in a chosen inertial laboratory frame. Scalars are real numbers with consistently assigned units; dimensions are not encoded in a units type system. Physical mass is fixed and positive. Several purely algebraic mass identities hold for every real m, and their Lean statements use that more general domain. The momentum ratio requires m ≠ 0.

Definitions:

- `gamma c v = 1 / sqrt(1 − (v/c)²)`.
- `proper c v = gamma c v * v`.
- `coordinate c u = u / sqrt(1 + (u/c)²)`.
- `momentum m c v = gamma c v * m * v`.
- `energy m c v = gamma c v * m * c²`.

The gamma normalization and inverse relations are proved from these definitions, not assumed. Forward physical results explicitly require c > 0 and |v| < c. The inverse speed bound requires c > 0 and permits **every signed real u**, including zero and negative values. Real numbers here are finite: neither an infinite proper velocity nor a photon state is included.

`proper_chain_rule` assumes actual derivative statements for laboratory position x(t) and a time parametrization t(τ), with dt/dτ = gamma, and proves the derivative of their composition is gamma v. It does not independently derive the proper-time metric or existence of that time parametrization. Future-directed timelike motion is the physical interpretation of the positive gamma clock rate.

The momentum and energy formulas are supplied model definitions; the companion verifies their mathematical consequences, not their experimental origin. The force calculation assumes constant m and uses laboratory time, not proper time. It proves no particular force law or acceleration history.

Lean division is totalized: division by zero returns zero. Its real square root is also a total function. Definitions therefore exist outside their physical domain, but the physical inversion and derivative theorems impose the necessary positivity and subluminality conditions. Do not interpret out-of-domain values of these definitions as physical predictions.

## Source-to-theorem map

Names are in namespace `ProperVelocity`; equation labels refer to the pinned TeX source.

| Source | Checked declarations | Meaning |
| --- | --- | --- |
| `eq:beta-gamma`, `eq:app-hyperbola` | `radicand_pos`, `gamma_pos`, `gamma_normalization`, `gamma_at_least_one` | Positive square-root domain, gamma > 0, gamma²(1 − β²) = 1 and gamma ≥ 1 |
| `eq:u-definition`, `eq:u-gamma-v` | `proper_chain_rule` | Actual chain rule for x(t(τ)); distinguishes the two time parameters |
| `eq:momentum`, `eq:momentum-u` | `momentum_eq_mass_proper`, `momentum_ratio` | p = mu and p/(mc) = u/c |
| `eq:mass-shell-u`, `eq:app-hyperbola` | `proper_hyperbola`, `mass_shell`, `gamma_from_proper` | gamma² − (u/c)² = 1, E² − p²c² = m²c⁴, and positive-root gamma |
| `eq:v-from-u`, `eq:app-inverse` | `coordinate_of_proper`, `inverse_sqrt_pos`, `inverse_radicand`, `gamma_of_coordinate`, `proper_of_coordinate` | Both inverse directions, with domains explicit |
| Finite-speed discussion after `eq:v-from-u` | `coordinate_bound`, `coordinate_sign`, `coordinate_odd`, `every_proper_velocity` | Strict |v| < c for every real u; sign and odd symmetry; every u is attained by a subluminal v |
| `eq:force-u` | `fixed_mass_force` | Scalar constant-mass derivative of mu; no force mechanism assumed |
| `eq:longitudinal-force` | `proper_derivative`, `longitudinal_acceleration`, `longitudinal_force` | Actual derivatives du/dv = gamma³, du/dt = gamma³a, and dp/dt = m gamma³a for differentiable one-dimensional motion |
| `eq:threshold` | `positive_threshold`, `negative_threshold` | u = ±c maps to v = ±c/sqrt(2); the general inverse theorems establish uniqueness |
| `eq:proxima-speed-values` | `example_gamma`, `example_proper` | v = 4c/5 gives gamma = 5/3 and u = 4c/3, for any c > 0 |
| `eq:proxima-lab-time`, `eq:proxima-proper-time`, `eq:proxima-average`, `eq:contracted-distance` | `example_journey` | Exact rational arithmetic conditional on the rounded 4.24 ly input: 5.30 yr, 3.18 yr, ratio 4/3, contracted distance 2.544 ly, and corresponding 3.18 yr |

Modules: `Algebra.lean` (14 theorems), `Calculus.lean` (5), `Examples.lean` (9). These counts include helper lemmas, not 28 independent physical claims.

## Interpretation and limits

Proper velocity uses laboratory displacement per traveler proper time. A value |u| > c is **not** superluminal coordinate motion, signal propagation, or velocity in the traveler's instantaneous rest frame. The strict coordinate-speed theorem applies to every finite u, not merely the 0.8c example.

Not formalized here: the Minkowski metric derivation of proper time, the limit |v| → c as |u| → infinity, rapidity/artanh identities, vector three-dimensional force/acceleration relations, variable-speed integral averages, strict clock inequality for nonzero v, or the full decimal comparison table. The sample trip proves arithmetic from a supplied rounded distance; it neither certifies the astronomical distance nor models acceleration, braking, gravity, or an attainable mission profile. The length-contraction example is arithmetic conditional on D' = D/gamma, not a separate spacetime derivation of that law. No empirical or new dynamical law is claimed.
