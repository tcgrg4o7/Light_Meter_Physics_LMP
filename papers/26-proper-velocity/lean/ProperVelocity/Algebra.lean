import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProperVelocity
noncomputable section

def gamma (c v : ℝ) := 1 / Real.sqrt (1 - (v / c) ^ 2)
def proper (c v : ℝ) := gamma c v * v
def coordinate (c u : ℝ) := u / Real.sqrt (1 + (u / c) ^ 2)
def momentum (m c v : ℝ) := gamma c v * m * v
def energy (m c v : ℝ) := gamma c v * m * c ^ 2

theorem radicand_pos {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    0 < 1 - (v / c) ^ 2 := by
  have hb := abs_lt.mp hv
  have hsq : v ^ 2 < c ^ 2 := by nlinarith
  have hd : (v / c) ^ 2 < 1 := by
    rw [div_pow]
    exact (div_lt_one (sq_pos_of_pos hc)).2 hsq
  linarith

theorem gamma_pos {c v : ℝ} (hc : 0 < c) (hv : |v| < c) : 0 < gamma c v := by
  unfold gamma
  exact one_div_pos.mpr (Real.sqrt_pos.2 (radicand_pos hc hv))

theorem gamma_normalization {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    gamma c v ^ 2 * (1 - (v / c) ^ 2) = 1 := by
  have hr := radicand_pos hc hv
  have hs := Real.sq_sqrt (le_of_lt hr)
  have hn := ne_of_gt (Real.sqrt_pos.2 hr)
  unfold gamma
  rw [div_pow, one_pow, hs]
  exact one_div_mul_cancel (ne_of_gt hr)

theorem proper_hyperbola {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    gamma c v ^ 2 - (proper c v / c) ^ 2 = 1 := by
  have h := gamma_normalization hc hv
  unfold proper
  calc
    gamma c v ^ 2 - (gamma c v * v / c) ^ 2 =
      gamma c v ^ 2 * (1 - (v / c) ^ 2) := by ring
    _ = 1 := h

theorem gamma_from_proper {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    gamma c v = Real.sqrt (1 + (proper c v / c) ^ 2) := by
  have h := proper_hyperbola hc hv
  have he : 1 + (proper c v / c) ^ 2 = gamma c v ^ 2 := by linarith
  rw [he, Real.sqrt_sq (le_of_lt (gamma_pos hc hv))]

theorem coordinate_of_proper {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    coordinate c (proper c v) = v := by
  unfold coordinate
  rw [← gamma_from_proper hc hv]
  unfold proper
  exact mul_div_cancel_left₀ v (ne_of_gt (gamma_pos hc hv))

theorem inverse_sqrt_pos (c u : ℝ) : 0 < Real.sqrt (1 + (u / c) ^ 2) := by
  apply Real.sqrt_pos.2
  positivity

theorem coordinate_bound {c : ℝ} (hc : 0 < c) (u : ℝ) : |coordinate c u| < c := by
  have hn := ne_of_gt hc
  have hs := inverse_sqrt_pos c u
  have he := Real.sq_sqrt (show 0 ≤ 1 + (u / c) ^ 2 by positivity)
  have hid : c ^ 2 * (1 + (u / c) ^ 2) = c ^ 2 + u ^ 2 := by field_simp
  have hlt : u ^ 2 < (c * Real.sqrt (1 + (u / c) ^ 2)) ^ 2 := by
    rw [mul_pow, he, hid]
    nlinarith [sq_pos_of_pos hc]
  have hab : |u| < c * Real.sqrt (1 + (u / c) ^ 2) := by
    have ha := abs_nonneg u
    have hb := mul_pos hc hs
    nlinarith [sq_abs u]
  unfold coordinate
  rw [abs_div, abs_of_pos hs]
  exact (div_lt_iff₀ hs).2 hab

theorem inverse_radicand {c : ℝ} (hc : 0 < c) (u : ℝ) :
    1 - (coordinate c u / c) ^ 2 = 1 / (1 + (u / c) ^ 2) := by
  have hn := ne_of_gt hc
  have hs := ne_of_gt (inverse_sqrt_pos c u)
  have he := Real.sq_sqrt (show 0 ≤ 1 + (u / c) ^ 2 by positivity)
  unfold coordinate
  rw [div_pow, div_pow, he]
  field_simp
  ring

theorem gamma_of_coordinate {c : ℝ} (hc : 0 < c) (u : ℝ) :
    gamma c (coordinate c u) = Real.sqrt (1 + (u / c) ^ 2) := by
  unfold gamma
  rw [inverse_radicand hc, Real.sqrt_div (by norm_num), Real.sqrt_one]
  simp

theorem proper_of_coordinate {c : ℝ} (hc : 0 < c) (u : ℝ) :
    proper c (coordinate c u) = u := by
  unfold proper
  rw [gamma_of_coordinate hc]
  unfold coordinate
  field_simp [ne_of_gt (inverse_sqrt_pos c u)]
  ring

theorem momentum_eq_mass_proper (m c v : ℝ) : momentum m c v = m * proper c v := by
  unfold momentum proper
  ring

theorem momentum_ratio {m c v : ℝ} (hm : m ≠ 0) (hc : c ≠ 0) :
    momentum m c v / (m * c) = proper c v / c := by
  rw [momentum_eq_mass_proper]
  field_simp
  ring

theorem mass_shell {m c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    energy m c v ^ 2 - momentum m c v ^ 2 * c ^ 2 = m ^ 2 * c ^ 4 := by
  have h := gamma_normalization hc hv
  have hn := ne_of_gt hc
  have hbase : gamma c v ^ 2 * c ^ 2 - gamma c v ^ 2 * v ^ 2 = c ^ 2 := by
    field_simp at h
    nlinarith [h]
  unfold energy momentum
  calc
    _ = m ^ 2 * c ^ 2 * (gamma c v ^ 2 * c ^ 2 - gamma c v ^ 2 * v ^ 2) := by ring
    _ = m ^ 2 * c ^ 4 := by rw [hbase]; ring

#print axioms radicand_pos
#print axioms gamma_pos
#print axioms gamma_normalization
#print axioms proper_hyperbola
#print axioms gamma_from_proper
#print axioms coordinate_of_proper
#print axioms inverse_sqrt_pos
#print axioms coordinate_bound
#print axioms inverse_radicand
#print axioms gamma_of_coordinate
#print axioms proper_of_coordinate
#print axioms momentum_eq_mass_proper
#print axioms momentum_ratio
#print axioms mass_shell
end
end ProperVelocity
