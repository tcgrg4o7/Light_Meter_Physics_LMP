# Manuscript 19: When the Horizon Spins — Lean companion

This companion checks Kerr root algebra, the Smarr split from explicit physical formula inputs, and the distinction between the rotational Smarr fraction and reversible extractable energy. Signed spin, zero spin, and extremal endpoints are handled explicitly.

## Reproduce

Install Lean through the official [Lean installation instructions](https://lean-lang.org/install/). From this directory:

```bash
lake exe cache get
bash check.sh
```

Lean is pinned to 4.19.0 and mathlib to v4.19.0, commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`; the manifest pins transitive dependencies. Do not update dependencies as part of routine checking. Initial downloads require internet access and several GB of storage. The repository-wide [Lean index](../../../LEAN.md) explains shared caching and automated checks.

`check.sh` builds the library and directly checks all three proof modules. All 71 named theorems (including helpers: Roots 23, Thermodynamics 26, Extraction 22) have axiom audits. The repository auditor rejects unfinished proofs, missing audits, and nonstandard reported axioms. The accepted standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. The complete project build and direct module checks passed locally using these pins, and the repository source/log audit passed for all 71 declarations. Hosted status should be checked for the exact commit in GitHub Actions. No workspace paths, generated files, tool installations, or build logs are committed.

## Source and assumptions

Pinned source: [manuscript 19 at commit 70490a9](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/70490a96b992f7acec79502b8bcf91ae433ac8fa/papers/19-when-the-horizon-spins/19.%20when%20the%20horizon%20spins.tex).

TeX SHA-256: `b14b46e5abf45619df3628b2f3467f25260d12bb979a280604d64a4a5e2fa020`.

Physical scope: four-dimensional, stationary, asymptotically flat, uncharged Kerr. `Parameters` supplies positive G, M, c, ħ and kB, and arbitrary signed J. The definitions τg = GM/c³, τJ = J/(Mc²), and χ = τJ/τg imply χ = cJ/(GM²). Admissible black-hole formulas explicitly assume |χ| ≤ 1; strict subextremal results use |χ| < 1. Quantities are real scalars with consistent units, not dimensionally typed objects.

The horizon equation in time-radius variables is supplied as a mathematical model: t² − 2τg t + (τg χ)² = 0. Lean proves the complete real-root classification of that polynomial, not that the Kerr metric solves Einstein's equations or that its roots are event horizons. The connection to physical horizons is a Kerr-geometry input. The equivalent square-root coordinate formulas are checked.

`omega`, `surfaceGravity`, and `area` are defined from the supplied Kerr expressions in coordinate-radius/time variables. `temperature` uses the semiclassical Hawking formula and `entropy` uses the Bekenstein–Hawking area law. Their reduced formulas and Smarr identity are **derived algebraically**, not inserted as assumptions. This does not derive Kerr geometry, the laws of black-hole mechanics, or quantum field theory.

The irreducible ratio is the positive square root sqrt((1+σ)/2); its mass scale is checked against the supplied Kerr area relation. `extractable = 1 − M_irr/M` is the ideal reversible-extraction bound as a model input, not a construction of an attainable extraction process. The strict inequality against the Smarr rotational fraction is an additional explicitly checked clarification of the paper's distinction.

## Source-to-theorem map

All declarations use namespace `Kerr`. `sigma x = sqrt(1 − x²)`; `outer g x = g(1+sigma x)`; `inner g x = g(1−sigma x)`.

| Source | Checked declarations/groups | Scope |
| --- | --- | --- |
| `eq:sigma-definition`, `eq:kerr-bound` | `spin_sq_le`, `sigma_nonneg`, `sigma_sq`, `sigma_le_one`, `sigma_lt_one`, `sigma_pos`, `sigma_zero`, `sigma_extremal`, `sigma_even` | Square-root domain, sign, bounds and endpoints |
| `eq:kerr-horizons`, `eq:horizon-times` | `root_factorization`, `root_classification`, `no_superextremal_root`, `root_exists_iff`, `scaled_root`, `coordinate_root_forms` | Both roots, no real roots when |χ| > 1, and exact square-root scaling |
| `eq:horizon-circle` and endpoint discussion | `horizon_circle`, `outer_pos`, `root_order`, `inner_pos_nonzero`, `subextremal_distinct`, `zero_spin_roots`, `extremal_roots`, `horizon_denominator` | Root ordering/positivity, circle identity, zero-spin and extremal cases |
| `eq:spin-times`, `eq:dimensionless-spin` | `tauG_pos`, `energy_pos`, `planckArea_pos`, `spin_formula`, `spin_time_relation`, `angular_momentum_relation`, `planck_area_time_relation` | Definitions, conversion identities, physical denominators |
| `eq:horizon-angular-velocity`, `eq:extremal-angular-velocity` | `denominator_pos`, `denominator_form`, `omega_form`, `omega_sign`, `zero_spin_omega`, `extremal_omega_abs` | Reduced angular velocity, its positive-sign equivalence with J, zero and absolute extremal value |
| `eq:surface-gravity`, `eq:kerr-temperature`, `eq:temperature-ratio` | `surface_gravity_form`, `temperature_form`, `temperature_ratio`, `temperature_pos`, `extremal_temperature` | Conditional temperature algebra; extremal endpoint is an algebraic extension |
| `eq:kerr-area`, `eq:smarr-kerr`, `eq:smarr-fractions`, `eq:area-smarr-link` | `area_form`, `thermal_smarr_fraction`, `rotational_smarr_fraction`, `smarr_identity`, `area_smarr_link` | Smarr derived from the explicit area/temperature/angular-velocity inputs; thermal σ and rotational 1−σ fractions |
| `eq:kerr-thermal-ratio` | `formal_thermal_ratio` | E*/(kB T) = 2π(1+σ)/σ only on the strict subextremal domain |
| `eq:irreducible-mass` | `irreducible_mass_square`, `irreducible_mass_area`, `irreducible_ratio_pos`, `irreducible_ratio_sq`, `irreducible_ratio_lower`, `irreducible_ratio_upper`, `irreducible_ratio_lt_one` | Positive root and agreement with the area definition |
| `eq:extractable-energy` and Smarr interpretation | `extraction_nonneg`, `extraction_upper`, `extraction_bounds`, `extraction_pos`, `extraction_lt_smarr`, `extraction_zero_iff`, `extraction_eq_smarr_iff` | 0 ≤ extraction ≤ 1−1/√2; strict extraction < Smarr fraction for nonzero admissible spin; equality only at zero spin |
| Zero-spin/extremal and signed-spin cases | `sqrt_half`, `irreducible_ratio_zero`, `extraction_zero`, `smarr_rot_zero`, `irreducible_ratio_extremal`, `extraction_extremal`, `smarr_rot_extremal`, `irreducible_ratio_even`, `extraction_even`, `smarr_rot_even` | Exact 1−1/√2 endpoint versus Smarr fraction 1, and reversal symmetry |

## Important interpretation limits

- At χ = 0, the formal inner root is zero. Physically this is the Schwarzschild singularity, **not an inner horizon**. For nonzero subextremal spin the inner root's Cauchy-horizon interpretation and instability issues are geometric/physical inputs, not proved here.
- τ± are Boyer–Lindquist radial coordinates divided by c, **not elapsed proper times**. ΩH is not rigid material rotation.
- The angular-velocity denominator stays positive, including extremality. The E*/(kB T) ratio instead requires σ > 0. No numerical value at T = 0 is assigned physical meaning, and no divergence or limiting theorem is claimed.
- Lean's real division and square root are totalized. Definitions exist outside physical domains, but the root-classification and physical identities restrict those domains. In particular, `sigma` returning zero outside |χ| ≤ 1 does not manufacture superextremal horizons; the separate no-real-root theorem excludes them.
- Smarr terms are not independent stored-energy reservoirs. At extremality their rotational fraction is 1, while the ideal extractable fraction is only 1−1/√2. The proof handles all nonzero signed admissible spins, not just a sample table.
- Not included: derivation of the Kerr metric, causal/global horizon structure, ergoregion observer physics, the differential first law, an area theorem or extraction process, QFT/Hawking derivation, bit-count interpretation, astrophysical numerical tables, accretion limits, orbit/ISCO co-location, or limits/monotonicity with varying spin. Neither angular-momentum quantization nor microscopic horizon tiles are asserted.

This is a source-mapped mathematical companion, not a proof of the whole manuscript or experimental validation of its physical inputs.
