# Manuscript 23: The Electron's Triangle — Lean companion

This companion checks exact mathematics of the manuscript's free-particle example at **v = 4c/5**. It includes genuine derivatives of the complex plane wave and its Klein–Gordon residual, not only substitution into a scalar dispersion polynomial. It does not establish experimentally that a physical electron is described completely by a scalar wave.

## Reproduce

Install Lean through the official [Lean installation instructions](https://lean-lang.org/install/), then from this directory run:

```bash
lake exe cache get
bash check.sh
```

For an already provisioned checkout, `bash check.sh` suffices. `lean-toolchain` pins Lean 4.19.0; `lake-manifest.json` pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0) and its dependencies. Keep the committed manifest; do not run `lake update` unless intentionally changing dependency resolution. Downloading dependencies requires internet access and several GB of disk space. No workspace-specific paths occur in the build configuration or script.

`check.sh` builds the library and rechecks each module directly, printing axiom dependencies for all 47 named theorems (including supporting lemmas). The build and direct checks were also run from the intended repository subfolder using the existing downloaded dependency cache; this is not a clean-machine installation test. All were checked with only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; there are no custom axioms or unfinished proofs. This is a local build result, not a claim about hosted CI. Generated files, logs, and tool installations are not part of the companion.

## Source and assumptions

Source: [manuscript 23 at commit 2e8713a](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/2e8713ac9da4e52e440ec152547838c22ec101a8/papers/23-the-electron-s-triangle/23-the-electron-s-triangle.tex).

Source SHA-256: `ff26d9f97e68362caf78846018ecbeb8240cf395b04b784b64b8bbf2ee1b6201`.

`Parameters` requires positive real mass m, light speed c, and reduced Planck constant ħ. No numerical value of any constant is assumed. Units are represented by consistent real-valued quantities rather than a formal dimensional-analysis type system. The 3–4–5 triangle is in energy units, not a spatial trajectory.

The supplied physical model consists of the special-relativistic free-particle Lagrangian, Lorentz time transformation, positive-energy square-root dispersion, E = γmc², p = γmv, plane-wave phase (px − Et)/ħ, and the operator conventions −iħ∂x and +iħ∂t. Lean proves their stated consequences and mutual consistency in this example; it does not derive these physical laws from experiments. Gamma is defined by its square root and proved to equal 5/3, not assumed to have that value. The canonical momentum is independently recovered by differentiating the Lagrangian at the selected velocity, and the Legendre expression is proved equal to E there.

Coordinates x and t range over all reals; the plane-wave amplitude is any constant complex number, including zero. Proper time is t/γ on the inertial path x = vt with coincident origins. Lorentz-transformed coordinate time equals this proper time only on that path. Lean's division is totalized (division by zero returns zero); positive parameter hypotheses ensure that physical denominators here are nonzero. Complex exponentials and derivatives are mathlib's mathematical functions, not floating-point approximations.

## Source-to-theorem map

Names below are in namespace `ElectronTriangle`. Equation labels refer to the pinned TeX source.

| Source claims | Checked declarations | Scope |
| --- | --- | --- |
| `eq:beta-gamma`, `eq:proper-time`, `eq:clock-rate-ratio` | `beta_sqrt`, `gamma_value`, `velocity_value`, `proper_time_value` | Exact selected speed, square root, gamma and proper-time relation |
| `eq:triangle-values`, `eq:mass-shell-derivation`, `eq:345-triangle` | `energy_value`, `momentum_value`, `energy_pos`, `momentum_pos`, `mass_shell`, `triangle_ratios` | Positive energy/momentum and exact 3–4–5 energy triangle |
| `eq:exact-kinetic`, `eq:light-cone-factors` | `kinetic_value`, `lightcone_values`, `lightcone_product` | K = 2mc²/3; lightcone factors 3 and 1/3 |
| `eq:free-lagrangian`, `eq:relativistic-momentum`, `eq:relativistic-energy` | `selected_radicand`, `selected_sqrt`, `lagrangian_derivative`, `lagrangian_value`, `legendre_energy` | Actual derivative of L(v), evaluated at v = 4c/5, and Legendre energy |
| `eq:lorentz-time`, `eq:boosted-phase-action`, `eq:phase-on-worldline` | `boosted_phase_action`, `lorentz_time_on_worldline`, `action_on_worldline` | All x,t for boosted action; x = vt for proper-time identity |
| `eq:celerity`, `eq:phase-velocity`, `eq:group-velocity` | `celerity_value`, `phase_velocity_value`, `group_slope_value`, `dispersion_at_momentum`, `dispersion_derivative` | Actual derivative of positive-energy dispersion at this momentum; phase speed 5c/4 is not signal speed |
| `eq:nonrel-kinetic`, `eq:rel-kinetic-again` | `nonrel_kinetic_value`, `nonrel_kinetic_ratio` | NR expression = 8mc²/9, ratio NR/exact = 4/3 (not relative excess 4/3) |
| `eq:compton-definitions`, `eq:lab-compton-scales` | `compton_period`, `lab_frequency`, `lab_wavelength` | h = 2πħ; period λC/c, lab frequency 5νC/3 and wavelength 3λC/4 |
| `eq:phase-angle`, `eq:phase-rate-fixed`, `eq:phase-rate-worldline-lab`, `eq:phase-rate-worldline-proper` | `phase_angle`, `fixed_phase_derivative`, `path_phase_derivative`, `proper_phase_derivative`, `fixed_phase_rate`, `path_phase_rate`, `proper_phase_rate` | Actual phase derivatives; cyclic rates use −1/(2π), with fixed position, lab-time path, and proper-time path distinguished |
| `eq:phase-convention`, `eq:momentum-eigenvalue`, `eq:energy-eigenvalue` | `wave_phase_convention`, `affine_exponential_derivative`, `wave_spatial_derivative`, `wave_temporal_derivative`, `momentum_operator_eigenvalue`, `energy_operator_eigenvalue` | Complex wave and actual first derivatives; signs −iħ∂x and +iħ∂t |
| `eq:klein-gordon`, `eq:kg-substitution` | `wave_spatial_second_derivative`, `wave_temporal_second_derivative`, `klein_gordon_plane_wave` | Actual second derivatives and pointwise vanishing of (1/c²)∂ttψ − ∂xxψ + (mc/ħ)²ψ for every x,t |

Files: `Kinematics.lean` (28 theorems), `Phase.lean` (10), and `PlaneWave.lean` (9). The name `nonrel_kinetic_ratio` denotes the ratio NR/exact; the relative excess is therefore 1/3.

## Deliberate limits

This is not a full formalization of the paper. It does not prove the general arbitrary-velocity relativistic theory, variational least-action principles, Taylor convergence or remainder bounds, construction or propagation of localized wave packets, KG current/density or its continuity equation, Dirac spinor dynamics, magnetic-force examples, numerical CODATA tables, or experimental claims. The scalar KG check is not a proof of the complete spin-1/2 electron theory. It neither normalizes the infinite plane wave nor interprets it as a localized particle. Physical assumptions, mathematical consequences, and empirical interpretation remain separate.
