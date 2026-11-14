import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
Checked with Lean 4.19.0. See README.md for exact coverage and limitations.
Source: manuscript 4, commit 0e76801d08ad946949e150299e32020330dd660c.
Real scalars use one consistent unit system; dimensional typing is not included.
The path claim below is a one-dimensional specialization, not full spacetime.
-/
namespace ComptonPilot

noncomputable def comptonFrequency (m c h : ℝ) : ℝ := m * c ^ 2 / h
noncomputable def energyFrequency (E h : ℝ) : ℝ := E / h
noncomputable def kineticFrequency (E m c h : ℝ) : ℝ := (E - m * c ^ 2) / h

/-- eq:gamma-frequency, conditional on the stated energy relation. -/
theorem energyFrequency_eq_gamma_mul_comptonFrequency
    (E γ m c h : ℝ) (hE : E = γ * m * c ^ 2) :
    energyFrequency E h = γ * comptonFrequency m c h := by
  unfold energyFrequency comptonFrequency
  rw [hE]
  ring

/-- First equality in eq:kinetic-frequency. -/
theorem kineticFrequency_eq_difference (E m c h : ℝ) :
    kineticFrequency E m c h =
      energyFrequency E h - comptonFrequency m c h := by
  unfold kineticFrequency energyFrequency comptonFrequency
  ring

/-- Last equality in eq:kinetic-frequency. -/
theorem kineticFrequency_eq_gamma_sub_one
    (E γ m c h : ℝ) (hE : E = γ * m * c ^ 2) :
    kineticFrequency E m c h = (γ - 1) * comptonFrequency m c h := by
  unfold kineticFrequency comptonFrequency
  rw [hE]
  ring

/-- Algebraic middle equality of eq:path-phase-rate, in one spatial dimension.
The normalization hypothesis must later be derived from the square-root
definition of gamma on the subluminal domain; this theorem does not do that.
-/
theorem pathFrequency_eq_compton_div_gamma
    (E p γ m c v h : ℝ) (hγ : γ ≠ 0)
    (hE : E = γ * m * c ^ 2) (hp : p = γ * m * v)
    (hNorm : γ ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2) :
    (E - p * v) / h = comptonFrequency m c h / γ := by
  have hprod : (E - p * v) * γ = m * c ^ 2 := by
    rw [hE, hp]
    calc
      (γ * m * c ^ 2 - γ * m * v * v) * γ =
          m * (γ ^ 2 * (c ^ 2 - v ^ 2)) := by ring
      _ = m * c ^ 2 := by rw [hNorm]
  apply (eq_div_iff hγ).2
  change (E - p * v) / h * γ = m * c ^ 2 / h
  calc
    (E - p * v) / h * γ = ((E - p * v) * γ) / h := by ring
    _ = m * c ^ 2 / h := by rw [hprod]

/-- Exact phase increment along x(t)=x₀+vt, written in cycles.
This is an affine identity, not yet a formal derivative or absolute-rate proof.
-/
theorem phaseCycles_along_inertial_path
    (E p h x₀ v t : ℝ) :
    (p * (x₀ + v * t) - E * t) / h =
      p * x₀ / h - ((E - p * v) / h) * t := by
  ring

#print axioms energyFrequency_eq_gamma_mul_comptonFrequency
#print axioms kineticFrequency_eq_difference
#print axioms kineticFrequency_eq_gamma_sub_one
#print axioms pathFrequency_eq_compton_div_gamma
#print axioms phaseCycles_along_inertial_path

end ComptonPilot
