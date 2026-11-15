import Kerr.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Kerr
noncomputable section

/-- M_irr/M for the supplied Kerr area model. -/
def irreducibleRatio (x : ℝ) := Real.sqrt ((1 + sigma x) / 2)
/-- Reversible-extraction upper fraction, not a construction of a physical process. -/
def extractable (x : ℝ) := 1 - irreducibleRatio x
/-- Fraction assigned to the rotational term in the Smarr identity. -/
def smarrRotFraction (x : ℝ) := 1 - sigma x

theorem sqrt_half : Real.sqrt (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one]

theorem irreducible_ratio_pos (x : ℝ) : 0 < irreducibleRatio x := by
  unfold irreducibleRatio
  apply Real.sqrt_pos.2
  have h := sigma_nonneg x
  linarith

theorem irreducible_ratio_sq (x : ℝ) : irreducibleRatio x ^ 2 = (1 + sigma x) / 2 := by
  unfold irreducibleRatio
  apply Real.sq_sqrt
  have h := sigma_nonneg x
  linarith

theorem irreducible_ratio_lower (x : ℝ) : 1 / Real.sqrt 2 ≤ irreducibleRatio x := by
  rw [← sqrt_half]
  apply Real.sqrt_le_sqrt
  have h := sigma_nonneg x
  linarith

theorem irreducible_ratio_upper {x : ℝ} (h : |x| ≤ 1) : irreducibleRatio x ≤ 1 := by
  have hs := sigma_le_one h
  have hr := irreducible_ratio_sq x
  have hp := irreducible_ratio_pos x
  nlinarith

theorem extraction_nonneg {x : ℝ} (h : |x| ≤ 1) : 0 ≤ extractable x := by
  unfold extractable
  linarith [irreducible_ratio_upper h]

theorem extraction_upper (x : ℝ) : extractable x ≤ 1 - 1 / Real.sqrt 2 := by
  unfold extractable
  linarith [irreducible_ratio_lower x]

theorem extraction_bounds {x : ℝ} (h : |x| ≤ 1) :
    0 ≤ extractable x ∧ extractable x ≤ 1 - 1 / Real.sqrt 2 :=
  ⟨extraction_nonneg h, extraction_upper x⟩

theorem irreducible_ratio_lt_one {x : ℝ} (h : |x| ≤ 1) (hx : x ≠ 0) :
    irreducibleRatio x < 1 := by
  have hs := sigma_lt_one h hx
  have hr := irreducible_ratio_sq x
  have hp := irreducible_ratio_pos x
  nlinarith

theorem extraction_pos {x : ℝ} (h : |x| ≤ 1) (hx : x ≠ 0) : 0 < extractable x := by
  unfold extractable
  linarith [irreducible_ratio_lt_one h hx]

/-- The reversible extraction fraction is strictly below the Smarr rotational
fraction at every nonzero admissible spin; the two quantities are not interchangeable. -/
theorem extraction_lt_smarr {x : ℝ} (h : |x| ≤ 1) (hx : x ≠ 0) :
    extractable x < smarrRotFraction x := by
  have hs0 := sigma_nonneg x
  have hs1 := sigma_lt_one h hx
  have hr := irreducible_ratio_sq x
  have hp := irreducible_ratio_pos x
  have hprod : 0 < (1 - sigma x) * (2 * sigma x + 1) :=
    mul_pos (by linarith) (by linarith)
  have hlt : sigma x < irreducibleRatio x := by nlinarith
  unfold extractable smarrRotFraction
  linarith

theorem irreducible_ratio_zero : irreducibleRatio 0 = 1 := by
  unfold irreducibleRatio
  rw [sigma_zero]
  norm_num

theorem extraction_zero : extractable 0 = 0 := by
  unfold extractable
  rw [irreducible_ratio_zero]
  ring

theorem smarr_rot_zero : smarrRotFraction 0 = 0 := by
  unfold smarrRotFraction
  rw [sigma_zero]
  ring

theorem extraction_zero_iff {x : ℝ} (h : |x| ≤ 1) : extractable x = 0 ↔ x = 0 := by
  constructor
  · intro he
    by_contra hx
    have hp := extraction_pos h hx
    linarith
  · intro hx
    subst x
    exact extraction_zero

theorem extraction_eq_smarr_iff {x : ℝ} (h : |x| ≤ 1) :
    extractable x = smarrRotFraction x ↔ x = 0 := by
  constructor
  · intro he
    by_contra hx
    have hlt := extraction_lt_smarr h hx
    linarith
  · intro hx
    subst x
    rw [extraction_zero, smarr_rot_zero]

theorem irreducible_ratio_extremal {x : ℝ} (h : |x| = 1) :
    irreducibleRatio x = 1 / Real.sqrt 2 := by
  unfold irreducibleRatio
  rw [sigma_extremal h]
  simp only [add_zero]
  exact sqrt_half

theorem extraction_extremal {x : ℝ} (h : |x| = 1) :
    extractable x = 1 - 1 / Real.sqrt 2 := by
  unfold extractable
  rw [irreducible_ratio_extremal h]

theorem smarr_rot_extremal {x : ℝ} (h : |x| = 1) : smarrRotFraction x = 1 := by
  unfold smarrRotFraction
  rw [sigma_extremal h]
  ring

theorem irreducible_ratio_even (x : ℝ) : irreducibleRatio (-x) = irreducibleRatio x := by
  unfold irreducibleRatio sigma
  rw [neg_sq]

theorem extraction_even (x : ℝ) : extractable (-x) = extractable x := by
  unfold extractable
  rw [irreducible_ratio_even]

theorem smarr_rot_even (x : ℝ) : smarrRotFraction (-x) = smarrRotFraction x := by
  unfold smarrRotFraction sigma
  rw [neg_sq]

#print axioms sqrt_half
#print axioms irreducible_ratio_pos
#print axioms irreducible_ratio_sq
#print axioms irreducible_ratio_lower
#print axioms irreducible_ratio_upper
#print axioms extraction_nonneg
#print axioms extraction_upper
#print axioms extraction_bounds
#print axioms irreducible_ratio_lt_one
#print axioms extraction_pos
#print axioms extraction_lt_smarr
#print axioms irreducible_ratio_zero
#print axioms extraction_zero
#print axioms smarr_rot_zero
#print axioms extraction_zero_iff
#print axioms extraction_eq_smarr_iff
#print axioms irreducible_ratio_extremal
#print axioms extraction_extremal
#print axioms smarr_rot_extremal
#print axioms irreducible_ratio_even
#print axioms extraction_even
#print axioms smarr_rot_even
end
end Kerr
