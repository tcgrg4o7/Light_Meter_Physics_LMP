# Lean companion index and checks

Ten of the 30 manuscripts currently have Lean companions. These check specified mathematical statements under explicit definitions and assumptions. They do not prove entire papers or establish physical interpretations experimentally. Each linked README records source mapping, domains, limitations, and reproduction instructions.

| Manuscript | Companion | Named theorems/lemmas* | Checked scope |
| --- | --- | ---: | --- |
| 04 · Compton Frequency | [Instructions and proofs](papers/04-compton-frequency/lean/) | 13 | Energy/frequency identities, gamma normalization, worldline phase derivative and positivity |
| 09 · Mass as a Time | [Instructions and proofs](papers/09-mass-as-a-time/lean/) | 30 | Gravitational/Schuler timescale identities, static lapse derivative, controlled exact identities and approximation distinction |
| 16 · The Smarr Relation | [Instructions and proofs](papers/16-the-smarr-relation/lean/) | 18 | Schwarzschild area, entropy, temperature, energy and Smarr identities conditional on the supplied model |
| 17 · Counting the Horizon | [Instructions and proofs](papers/17-counting-the-horizon/lean/) | 22 | Horizon count, entropy/bit conversion and equipartition algebra with stated assumptions |
| 19 · When the Horizon Spins | [Instructions and proofs](papers/19-when-the-horizon-spins/lean/) | 71 | Kerr root classification, conditional Smarr fractions, signed-spin endpoints and strict extraction-versus-Smarr inequality |
| 23 · The Electron's Triangle | [Instructions and proofs](papers/23-the-electron-s-triangle/lean/) | 47 | Exact 3–4–5 example, Lagrangian/dispersion and phase derivatives, complex plane-wave operators and Klein–Gordon residual |
| 26 · Proper Velocity | [Instructions and proofs](papers/26-proper-velocity/lean/) | 28 | Signed inverse velocity maps, strict subluminal coordinate bound, chain rule, longitudinal derivatives and example arithmetic |
| 28 · Three Powers of Radius | [Instructions and proofs](papers/28-three-powers-of-radius/lean/) | 8 | Derivative ladder, independent circular balance, and radius doubling |
| 29 · Kepler’s Law in Logarithms | [Instructions and proofs](papers/29-kepler-in-logarithms/lean/) | 7 | Conditional ellipse period, semimajor-axis log slope and full-period intercept |
| 30 · Schwarzschild Tides | [Instructions and proofs](papers/30-tidal-deformation/lean/) | 11 | Tidal trace, initial volume derivatives, conditional curvature contraction and horizon scalings |
| **Total** | **10 companions** | **255** | **Supporting lemmas included; not 255 independent physical claims** |

*Counts are source declarations, not a measure of scientific coverage. The other 20 manuscripts have no companion indexed here. Existing historical module names are retained for compatibility; new infrastructure has no “pilot” naming.

## Run everything locally

Install Lean via the official [Lean installation instructions](https://lean-lang.org/install/). All ten projects currently pin Lean 4.19.0 and the same mathlib v4.19.0 commit. Python 3.10 or newer and Bash are also needed.

For each directory in [`scripts/lean-projects.txt`](scripts/lean-projects.txt), run `lake exe cache get` inside that directory once to provision its pinned dependencies. Then, from the repository root:

```bash
bash scripts/check-lean.sh
```

This runs audit unit tests, each original `check.sh` (library build plus direct module checking), and source/log audits. A nonzero exit from any build or audit fails the aggregate command. It does not update manifests or modify proofs. The per-paper manuals and commands remain usable independently.

For a fresh checkout, an optional disk/download optimization shares identical dependency packages:

```bash
python3 scripts/prepare-lean-cache.py
(cd papers/04-compton-frequency/lean && lake exe cache get)
bash scripts/check-lean.sh
```

The preparation script first verifies the project registry and identical package pins/toolchains. It links only `.lake/packages` to `.lean-cache/packages`; each project's build outputs remain separate. It refuses to overwrite existing package directories. Use separate dependency caches if projects acquire different pins; do not force incompatible versions into the shared directory. Several GB of disk space and initial network downloads are required.

## Automated checks

[GitHub Actions workflow](.github/workflows/lean.yml) · [Run history](https://github.com/tcgrg4o7/Light_Meter_Physics_LMP/actions/workflows/lean.yml)

The workflow runs on relevant pushes to `main`, pull requests, and manual dispatch. A single Linux job checks all ten projects sequentially, provisions dependencies once, and caches the pinned toolchain/shared packages. New pushes cancel superseded runs on the same ref. Documentation-only changes outside this index and proof-related paths do not trigger an expensive build.

Permissions are read-only (`contents: read`), checkout credentials are not persisted, and the workflow neither publishes nor commits anything. External actions are pinned to full commit hashes; Elan installation uses an official fixed release with a recorded SHA-256 checksum. There is no `pull_request_target` trigger or secret-dependent step. This workflow does not configure branch protection or make the check mandatory for merging.

A passing check requires:

1. Successful builds and direct Lean checks using each project's pinned environment.
2. No `sorry`, `admit`, custom axiom declarations, unsafe/native proof shortcuts, or unsupported proof-declaration forms in the companion sources.
3. A `#print axioms` audit for every named theorem/lemma, with a corresponding report in the Lean output.
4. No reported axioms except Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx`, missing reports, and compilation errors fail.

The Python auditor is deliberately conservative for this repository's current source style. It is a lint plus a check of Lean's reports, **not a full Lean parser, malicious-code sandbox, or proof of statement fidelity**. New syntax may require updating it and its negative tests. Proofs still need human review for correct hypotheses, physical meaning, and manuscript coverage. There is no numerical/experimental validation stage or automated check that a later manuscript edit still matches the pinned proof companion.

The initial aggregate build and audits were tested locally with an existing dependency cache. Hosted CI status must be read from the linked run history for the exact commit; adding this workflow is not itself evidence that a hosted run passed.

## Adding a companion

1. Add a self-contained project and accurate source-mapped README under its manuscript's `lean/` directory.
2. Keep toolchain and dependency pins, and provide `check.sh` that builds the library and directly checks every proof module.
3. Include an axiom report for every theorem/lemma and run the audit unit tests.
4. Add the directory to `scripts/lean-projects.txt` and this table. The cache-preparation step rejects unregistered projects or divergent shared pins.
5. Run `bash scripts/check-lean.sh`, then inspect the hosted run for the commit before reporting CI success.
