# Schwarzschild Tides: Lean companion

Source: [published manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/69aa272876b3d15f4bc80d02d22e2d11df46d615/papers/30-tidal-deformation/30-tidal-deformation.tex), pinned to commit `69aa272`. The Lean statements check consequences of the model assumptions below, not the physical model itself.

## Checked claims

- `trace_free`, `initial_volume_rate`, and `initial_volume_acceleration`: the Schwarzschild (+2, −1, −1) acceleration pattern and both vanishing volume derivatives at initially comoving release, conditional on the axis accelerations and differentiability. The volume is proportional to the product of three semiaxes. This is local, not a volume-conservation law.
- `contraction_eq`, `invariant_scale`, and `scale_from_invariant`: `eq:kretschmann` and `eq:invariant-scale` using the six supplied orthonormal components, their four ordered copies each, and the metric-sign products. The result is 48 times the squared length-based scale; the inverse uses the nonnegative branch.
- `horizon_scale`, `horizon_acceleration_coefficients`, `horizon_curvature`, and `horizon_mass_scaling`: `eq:horizon-values`, using t_r = 2τ_g at each hole's own horizon. At fixed c, a mass multiplier s changes the tidal scale by s⁻² and the scalar by s⁻⁴.
- `plane_wave_contrast`: both patterns have zero trace but differ for positive mass scale. This is only a comparison of the specified tidal coefficients.

The components are inputs, not derived here from the metric. This does not recover a general tidal tensor from a scalar, model nonspherical or rotating black holes, or certify the numerical examples.

## Reproduce

Use the pinned Lean 4 and mathlib versions in this directory. With Lake available:

```sh
lake exe cache get
bash check.sh
```

The script builds the project and checks `SchwarzschildTides.lean` directly to print all axiom reports. The [repository Lean index](../../../LEAN.md) documents the combined audit.
