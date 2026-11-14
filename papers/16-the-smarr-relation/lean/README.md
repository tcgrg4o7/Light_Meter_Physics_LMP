# Manuscript 16: Schwarzschild Smarr relation

This companion derives `2 T_H S_BH = M c²` from the paper's stated model inputs,
and separately checks the quadratic-entropy/first-law explanation of the factor
two. It is a first-principles derivation **within that explicit model**, not a
derivation of the model itself from Einstein's equations or quantum field theory.

**Verification:** all 18 formal statements passed `lake build` and direct Lean
checking on 2026-11-14. Their axiom reports list only `propext`,
`Classical.choice`, and `Quot.sound`. No unfinished proofs or custom axioms.

## Source and reproducibility

- [Pinned manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/219958afcf921b669f07b9b5631520a22d2d5fb4/papers/16-the-smarr-relation/16.%20the%20smarr%20relation.tex).
- Commit: `219958afcf921b669f07b9b5631520a22d2d5fb4`.
- Source SHA-256: `8a00b054da6d63345bcd7e0622561313173b324af8e333ca1e2ad9952f43b8f7`.
- Lean 4.19.0, mathlib v4.19.0 at `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `lake-manifest.json` locks resolved dependencies.

## Explicit physical input, not a theorem about the world

The domain is an uncharged, nonrotating, four-dimensional, asymptotically flat
Schwarzschild black hole with the standard semiclassical temperature at infinity
and the Bekenstein-Hawking area normalization. The formal constants structure
requires positive `G`, `c`, `hbar`, and `kB`; the physical product and thermal
claims require `M > 0`. The code uses mathlib's actual real number `Real.pi`.

The input definitions are:

1. `r_s = 2 G M / c²` and `tau_g = G M / c³`.
2. Spherical horizon area `A = 4 pi r_s²`.
3. Planck area `l_P² = hbar G / c³`.
4. Absolute area entropy `S = kB A / (4 l_P²)`.
5. Hawking temperature `T = hbar c³ / (8 pi G M kB)`.
6. Mass energy `E = M c²`.

The proof does not assume the target product identity. Entropy is defined through
area and Planck area, and its reduced mass formula is proved before cancellation.
Encoding a physical law as a definition does not experimentally validate it.
Real-valued arithmetic uses a common unit system; dimensional types are not used.

## Source-to-proof map

| Manuscript equation | Formal statements |
|---|---|
| `eq:radius-time-identity` | `radius_time` |
| `eq:horizon-area` | `area_mass` |
| `eq:area-law`, `eq:entropy-mass` | area-based `entropy` definition, `entropy_mass` |
| `eq:hawking-temperature` | `temperature` input definition, `temperature_time` |
| `eq:smarr` | `smarr` |
| `eq:thermal-timescale` | `thermal_time` |
| `eq:thermal-frequency` | `thermal_frequency`, with `h = 2*pi*hbar` explicit |
| `eq:entropy-difference` | `entropy_difference` |
| `eq:first-law` | `entropy_hasDerivAt`, `energy_hasDerivAt`, `first_law_mass`, `first_law` |
| `eq:entropy-slope` | `entropy_energy`, `quadratic_entropy_hasDerivAt`, `quadratic_entropy_slope` |
| `eq:scaling-derivation` | `smarr_from_first_law` |
| Paragraph on additive normalization | `offset_entropy_hasDerivAt`, `offset_smarr` |

## Two complementary arguments

**Direct model calculation.** Substitute radius into area, area into entropy,
then multiply the derived entropy formula by twice the specified Hawking
temperature. The result is `M c²`. The derivatives of the same model functions
also satisfy `dE/dM = T dS/dM`.

**Scaling argument.** For `S(E)=C E²`, prove its derivative and impose the
differential first-law hypothesis `T * dS/dE = 1`. Deduce `E=2TS` algebraically.
The abstract theorem is conditional on that first law; it does not derive a
thermodynamic law from polynomial differentiation.

An additive offset `S0` leaves the derivative unchanged but changes the product:
`2T(C E² + S0) = E + 2T S0`. Thus the differential first law alone cannot fix the
absolute entropy needed for the usual Smarr equality. The area-law normalization
is a genuine model input, not a dispensable convention silently dropped.

## Checking

Install [Elan/Lean](https://lean-lang.org/install/) and put `lake` on PATH.
From the repository root, run:

```bash
cd papers/16-the-smarr-relation/lean
bash check.sh
```

Lake restores the pinned dependencies and compiles
what is needed; the first build may take time. Optional precompiled mathlib
caches can be obtained with `lake exe cache get`. Do not update the pinned
dependencies merely to reproduce this snapshot.

`check.sh` builds the root module, then directly checks the proof file and prints
all theorem axiom dependencies. No `sorry`, custom axiom, numerical oracle or
unchecked tactic result is used. `noncomputable` definitions use abstract real
numbers; they do not bypass proof checking or supply numerical approximations.

Lean division is total, including at zero. Some algebraic helper results are
valid outside the physical domain; physical interpretation still requires the
positive constants and positive mass stated above.

## Limits

Not formalized: the Einstein field equations, derivation of the Schwarzschild
solution or spherical area from differential geometry, Hawking's field-theory
calculation, microscopic entropy, solar/Earth numerical examples and measurement
uncertainties, the general exponent-n scaling claim, or rotating/charged/higher-
dimensional/non-asymptotically-flat generalizations. No observed Hawking radiation
or new energy reservoir is claimed. Entropy differences are checked by algebra;
an integration theorem with boundary conditions is not included.
