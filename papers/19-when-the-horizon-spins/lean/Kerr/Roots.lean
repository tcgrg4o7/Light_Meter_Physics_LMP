import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Kerr
noncomputable section

def sigma (x : ℝ) := Real.sqrt (1 - x ^ 2)
def outer (g x : ℝ) := g * (1 + sigma x)
def inner (g x : ℝ) := g * (1 - sigma x)
def horizonPolynomial (g x t : ℝ) := t ^ 2 - 2 * g * t + (g * x) ^ 2

theorem spin_sq_le {x : ℝ} (h : |x| ≤ 1) : x ^ 2 ≤ 1 := by
  have ha := abs_le.mp h
  nlinarith

theorem sigma_nonneg (x : ℝ) : 0 ≤ sigma x := Real.sqrt_nonneg _
theorem sigma_sq {x : ℝ} (h : |x| ≤ 1) : sigma x ^ 2 = 1 - x ^ 2 := by
  exact Real.sq_sqrt (by linarith [spin_sq_le h])
theorem sigma_le_one {x : ℝ} (h : |x| ≤ 1) : sigma x ≤ 1 := by
  nlinarith [sigma_sq h, sigma_nonneg x, sq_nonneg x]
theorem sigma_lt_one {x : ℝ} (h : |x| ≤ 1) (hx : x ≠ 0) : sigma x < 1 := by
  nlinarith [sigma_sq h, sigma_nonneg x, sq_pos_of_ne_zero hx]
theorem sigma_pos {x : ℝ} (h : |x| < 1) : 0 < sigma x := by
  apply Real.sqrt_pos.2
  have ha := abs_lt.mp h
  nlinarith
theorem sigma_zero : sigma 0 = 1 := by norm_num [sigma]
theorem sigma_extremal {x : ℝ} (h : |x| = 1) : sigma x = 0 := by
  have hs : x ^ 2 = 1 := by nlinarith [sq_abs x]
  simp [sigma, hs]
theorem sigma_even (x : ℝ) : sigma (-x) = sigma x := by simp [sigma]

theorem root_factorization {g x : ℝ} (h : |x| ≤ 1) (t : ℝ) :
    horizonPolynomial g x t = (t - outer g x) * (t - inner g x) := by
  unfold horizonPolynomial outer inner
  nlinarith [congrArg (fun z : ℝ => g ^ 2 * z) (sigma_sq h)]
theorem root_classification {g x : ℝ} (h : |x| ≤ 1) (t : ℝ) :
    horizonPolynomial g x t = 0 ↔ t = outer g x ∨ t = inner g x := by
  rw [root_factorization h, mul_eq_zero, sub_eq_zero, sub_eq_zero]
theorem no_superextremal_root {g x : ℝ} (hg : 0 < g) (h : 1 < |x|) (t : ℝ) :
    horizonPolynomial g x t ≠ 0 := by
  have hx : 1 < x ^ 2 := by nlinarith [sq_abs x]
  have hp : 0 < g ^ 2 * (x ^ 2 - 1) := mul_pos (sq_pos_of_pos hg) (by linarith)
  unfold horizonPolynomial
  nlinarith [sq_nonneg (t - g)]
theorem root_exists_iff {g x : ℝ} (hg : 0 < g) :
    (∃ t, horizonPolynomial g x t = 0) ↔ |x| ≤ 1 := by
  constructor
  · rintro ⟨t, ht⟩
    by_contra h
    exact no_superextremal_root hg (lt_of_not_ge h) t ht
  · intro h
    exact ⟨outer g x, (root_classification h _).2 (Or.inl rfl)⟩
theorem horizon_circle {g x : ℝ} (h : |x| ≤ 1) :
    (outer g x - g) ^ 2 + (g * x) ^ 2 = g ^ 2 := by
  unfold outer
  nlinarith [congrArg (fun z : ℝ => g ^ 2 * z) (sigma_sq h)]
theorem outer_pos {g x : ℝ} (hg : 0 < g) : 0 < outer g x := by
  unfold outer
  exact mul_pos hg (by linarith [sigma_nonneg x])
theorem root_order {g x : ℝ} (hg : 0 < g) (h : |x| ≤ 1) :
    0 ≤ inner g x ∧ inner g x ≤ outer g x := by
  unfold inner outer
  constructor
  · exact mul_nonneg (le_of_lt hg) (by linarith [sigma_le_one h])
  · nlinarith [sigma_nonneg x]
theorem inner_pos_nonzero {g x : ℝ} (hg : 0 < g) (h : |x| ≤ 1) (hx : x ≠ 0) :
    0 < inner g x := by
  exact mul_pos hg (by linarith [sigma_lt_one h hx])
theorem subextremal_distinct {g x : ℝ} (hg : 0 < g) (h : |x| < 1) :
    inner g x < outer g x := by
  unfold inner outer
  nlinarith [sigma_pos h]
theorem zero_spin_roots (g : ℝ) : outer g 0 = 2 * g ∧ inner g 0 = 0 := by
  simp [outer, inner, sigma_zero]
  ring
theorem extremal_roots {g x : ℝ} (h : |x| = 1) : outer g x = g ∧ inner g x = g := by
  simp [outer, inner, sigma_extremal h]
theorem horizon_denominator {g x : ℝ} (h : |x| ≤ 1) :
    outer g x ^ 2 + (g * x) ^ 2 = 2 * g ^ 2 * (1 + sigma x) := by
  unfold outer
  nlinarith [congrArg (fun z : ℝ => g ^ 2 * z) (sigma_sq h)]

theorem scaled_root {g x : ℝ} (hg : 0 < g) (h : |x| ≤ 1) :
    Real.sqrt (g ^ 2 - (g * x) ^ 2) = g * sigma x := by
  have hp := mul_nonneg (le_of_lt hg) (sigma_nonneg x)
  have hs := congrArg (fun z : ℝ => g ^ 2 * z) (sigma_sq h)
  have he : g ^ 2 - (g * x) ^ 2 = (g * sigma x) ^ 2 := by
    dsimp at hs
    nlinarith only [hs]
  rw [he, Real.sqrt_sq hp]

theorem coordinate_root_forms {g x : ℝ} (hg : 0 < g) (h : |x| ≤ 1) :
    outer g x = g + Real.sqrt (g ^ 2 - (g * x) ^ 2) ∧
    inner g x = g - Real.sqrt (g ^ 2 - (g * x) ^ 2) := by
  rw [scaled_root hg h]
  unfold outer inner
  constructor <;> ring

#print axioms spin_sq_le
#print axioms sigma_nonneg
#print axioms sigma_sq
#print axioms sigma_le_one
#print axioms sigma_lt_one
#print axioms sigma_pos
#print axioms sigma_zero
#print axioms sigma_extremal
#print axioms sigma_even
#print axioms root_factorization
#print axioms root_classification
#print axioms no_superextremal_root
#print axioms root_exists_iff
#print axioms horizon_circle
#print axioms outer_pos
#print axioms root_order
#print axioms inner_pos_nonzero
#print axioms subextremal_distinct
#print axioms zero_spin_roots
#print axioms extremal_roots
#print axioms horizon_denominator
#print axioms scaled_root
#print axioms coordinate_root_forms
end
end Kerr
