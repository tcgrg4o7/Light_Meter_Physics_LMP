# Manuscript 17: counting the horizon

Lean 4 companion for the Schwarzschild area ratio, entropy-unit conversions,
mass-energy identities and frequency forms. Count-like quantities are real
numbers: no integer tile count, binary memory cell or microscopic mode is assumed.

## Verification and dependencies

All 22 named statements passed `lake build` and direct Lean checking on
2026-11-14. Axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`: no unfinished proofs or custom axioms.

- Lean 4.19.0, selected by `lean-toolchain`.
- mathlib v4.19.0, resolved commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- `lake-manifest.json` locks dependencies. This project is self-contained apart
  from those dependencies; it does not import the earlier manuscript companions.
- [Pinned manuscript](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/blob/a0854589764f512c886f1d9e7328956f321df836/papers/17-counting-the-horizon/17.%20counting%20the%20horizon.tex).
- Source SHA-256: `3a94926b546b4eb89d469fd56b96666e1abfbbf3bb27375aaf03bf5bf6747b67`.

## Physical inputs and exact mathematical scope

The `Constants` structure requires positive `G`, `c`, `hbar`, and `kB`.
The physical energy identities require positive mass. Definitions encode the
paper's standard four-dimensional, asymptotically flat, uncharged, nonrotating
Schwarzschild model:

- `r_s = 2 G M / c²`, `A = 4 pi r_s²`, `l_P² = hbar G / c³`.
- Area ratio `n_A = A/l_P²` and entropy `S = kB A/(4 l_P²)`.
- `T_H = hbar c³/(8 pi G M kB)`, normalized at infinity.
- `E = M c²`, `h = 2 pi hbar`.
- Nats `S/kB`; bits `S/(kB ln 2)`.

The code uses mathlib's actual `Real.pi` and `Real.log 2`, and proves `ln 2 > 0`.
These are not arbitrary symbols whose desired values are supplied as assumptions.
The physical formulas themselves are model inputs, not conclusions derived from
Einstein's equations, quantum field theory or microscopic statistical mechanics.
All scalars use consistent units; dimensional types are not formalized.

## Source-to-theorem ledger

| Source | Checked statements and meaning |
|---|---|
| `eq:area-and-planck-area`, `eq:area-count` | `area_mass`, `area_ratio_mass`: derive `n_A = 16 pi G M²/(hbar c)` from radius and area |
| `eq:entropy-nats` | `entropy_nats`: `S/kB = n_A/4` |
| `eq:entropy-bits` | `entropy_bits`, `nats_from_bits`, `area_from_bits`: exact unit conversion, including `n_A = 4 ln 2 n_bit` |
| Positive physical domain | `log_two_pos`, `area_ratio_pos`, `entropy_bits_pos`, `temperature_pos` |
| `eq:area-count-energy` | `area_energy_identity`: `E = (n_A/2) kB T_H` |
| `eq:smarr` | `smarr`: `E = 2 T_H S` |
| `eq:bit-energy` | `bit_energy_identity`: `E = 2 ln 2 n_bit kB T_H` |
| `eq:frequencies`, `eq:frequency-identity` | `area_frequency_identity`, `bit_frequency_identity`, `angular_frequency`: both frequency identities and `E/hbar = 2 pi (E/h)` |
| Mass-scaling discussion | `area_ratio_scaling`, `bits_scaling`, `temperature_scaling`, `mass_frequency_scaling`, `thermal_frequency_scaling` |
| Equipartition-form discussion | `coefficient_conversion`: `n_A/2 = 2 ln 2 n_bit`, explaining why changing the unit changes the coefficient |

The derivation proceeds from area and Planck area, not by assuming the target
energy equality. It then re-expresses the same identity in entropy-bit and
frequency units. Under a positive mass rescaling `M -> aM`, area ratio and bits
scale by `a²`, temperature and thermal frequency by `1/a`, and mass frequency by
`a`. Some algebraic helper identities hold on wider domains because Lean division
is total, including at zero; those extra cases are not physical black holes.

## What the equipartition-shaped identity does not establish

`E = (n_A/2) kB T_H` has the algebraic shape of classical equipartition. The
formalization proves that equation under the specified Schwarzschild formulas.
It does not establish that `n_A` counts independent quadratic degrees of freedom,
that a classical equilibrium mode model exists, or that the horizon stores
individually addressable bits. No reverse derivation of Newtonian gravity or
historical attribution is made.

The first-law derivative/scaling argument is not repeated in this project; the
[Manuscript 16 companion](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/tree/a0854589764f512c886f1d9e7328956f321df836/papers/16-the-smarr-relation/lean)
checks that argument and the additive-entropy-normalization issue. This project's
energy identities are independently proved from its own model definitions.

Not checked here: rounded decimal conversion factors, solar/Earth numerical
tables or measurement uncertainty, literal area quantization, microstate models,
Kerr/charged/higher-dimensional generalizations, observed Hawking radiation, or
whether the frequency scales are emitted spectral peaks or horizon oscillations.

## Reproduce

Install [Elan/Lean](https://lean-lang.org/install/) and put `lake` on PATH. From
the repository root:

```bash
cd papers/17-counting-the-horizon/lean
bash check.sh
```

Lake restores pinned dependencies. The first build may take time and requires
network access for tooling/dependencies; precompiled mathlib caches are optional.
Do not run `lake update` merely to reproduce the locked snapshot. After setup,
proof checking runs locally. The script uses the caller's Lean installation,
builds the root module and directly checks `Horizon/Counting.lean`, printing all
22 axiom reports. A successful check exits zero. No GitHub Actions execution is
implied by the recorded local check.

`noncomputable` marks abstract real-number definitions rather than executable
floating-point calculations. It does not disable kernel proof checking.
