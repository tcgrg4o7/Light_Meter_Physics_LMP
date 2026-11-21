# Kepler’s Law in Logarithms: Lean companion

Source: [published manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/69aa272876b3d15f4bc80d02d22e2d11df46d615/papers/29-kepler-in-logarithms/29-kepler-in-logarithms.tex), pinned to commit `69aa272`. The Lean statements check consequences of the model assumptions below, not the physical model itself.

## Checked claims

- `ellipse_period`: the period squared in `eq:ellipse-period`, using the ellipse area πab, the constant areal rate h/2, and the supplied equalities for the semilatus rectum. The eccentricity-dependent b cancels. Here a and b belong to the relative orbit, and μ denotes G(M₁ + M₂), not the field of either body alone.
- `light_time_law` and `normalized_powers`: the time-unit and dimensionless forms in `eq:elliptical-time-law` and `eq:dimensionless-law`, with t_a = a/c, τ_g = μ/c³, and τ_S = T_S/(2π).
- `logarithmic_slope` and `full_period_intercept`: slope 2/3 on positive dimensionless ratios, and the intercept shift in `eq:full-period-intercept`.
- `ellipse_log_law`: connects the ellipse inputs directly to `eq:elliptical-log-law`.
- `eightfold_time_fourfold_size`: an exact special case of `eq:orbit-ratio`.

This companion does not derive the conic orbit or the conserved areal rate from Newton's equations, check measured orbital elements, or claim that mean anomaly is the physical angular sweep of an ellipse.

## Reproduce

Use the pinned Lean 4 and mathlib versions in this directory. With Lake available:

```sh
lake exe cache get
bash check.sh
```

The script builds the project and checks `KeplerLogarithms.lean` directly to print all axiom reports. The [repository Lean index](../../../LEAN.md) documents the combined audit.
