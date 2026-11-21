# Three Powers of Radius: Lean companion

Source: [published manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/69aa272876b3d15f4bc80d02d22e2d11df46d615/papers/28-three-powers-of-radius/28-three-powers-of-radius.tex), pinned to commit `69aa272`. The Lean statements check consequences of the model assumptions below, not the physical model itself.

## Checked claims

- `compactness_derivative`, `inverse_time_derivative`, `ladder`, and `second_derivative`: the full derivative chain in `eq:three-rungs` and `eq:derivative-ladder`. Differentiation is with respect to radius light-time at fixed mass, not an observer's proper time.
- `circular_balance` and `light_time_conversion`: the orbital scale of `eq:newtonian-orbit-rate` is obtained separately from Newtonian circular force balance; it is not defined as the derivative. The end-to-end theorem `circular_rate_is_half_second_derivative` shows that the two routes yield the same third rung after changing units.
- `doubling`: exact factors in `eq:doubling-check`.

The inputs are the inverse-square model and the circular balance equation. This companion adds the differentiated radius ladder to the earlier Paper 9 timescale work; it does not rederive the Schwarzschild geodesic appendix, certify numerical tables, or prove a Schuler oscillator model.

## Reproduce

Use the pinned Lean 4 and mathlib versions in this directory. With Lake available:

```sh
lake exe cache get
bash check.sh
```

The script builds the project and checks `RadiusPowers.lean` directly to print all axiom reports. The [repository Lean index](../../../LEAN.md) documents the combined audit.
