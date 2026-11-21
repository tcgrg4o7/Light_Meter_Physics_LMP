import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace KeplerLogarithms

noncomputable section

/-- Newtonian ellipse: πab is the area, h/2 is its areal rate, and b²/a = h²/μ.
    The result uses the relative orbit and μ = G(M₁ + M₂). -/
theorem ellipse_period (a b h μ : ℝ) (ha : 0 < a) (hh : 0 < h) (hμ : 0 < μ)
    (hp : b ^ 2 / a = h ^ 2 / μ) :
    (Real.pi * a * b / (h / 2)) ^ 2 = 4 * Real.pi ^ 2 * a ^ 3 / μ := by
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hh)
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hb : b ^ 2 / h ^ 2 = a / μ := by
    apply (div_eq_div_iff hh2 hμ0).2
    simpa [mul_comm] using (div_eq_div_iff (ne_of_gt ha) hμ0).1 hp
  calc
    (Real.pi * a * b / (h / 2)) ^ 2 =
        (4 * Real.pi ^ 2 * a ^ 2) * (b ^ 2 / h ^ 2) := by ring
    _ = 4 * Real.pi ^ 2 * a ^ 3 / μ := by rw [hb]; ring

theorem light_time_law (a μ c τS : ℝ) (hc : 0 < c) (hμ : 0 < μ)
    (period : τS ^ 2 = a ^ 3 / μ) :
    (a / c) ^ 3 = (μ / c ^ 3) * τS ^ 2 := by
  rw [period]
  field_simp [ne_of_gt hc, ne_of_gt hμ]
  ring

theorem normalized_powers (ta tg ts : ℝ) (hg : 0 < tg)
    (law : ta ^ 3 = tg * ts ^ 2) :
    (ta / tg) ^ 3 = (ts / tg) ^ 2 := by
  calc
    (ta / tg) ^ 3 = ta ^ 3 / tg ^ 3 := by ring
    _ = (ts / tg) ^ 2 := by rw [law]; field_simp [ne_of_gt hg]; ring

theorem logarithmic_slope (ta tg ts : ℝ) (_ha : 0 < ta) (hg : 0 < tg)
    (_hs : 0 < ts) (law : ta ^ 3 = tg * ts ^ 2) :
    Real.log (ta / tg) = (2 / 3 : ℝ) * Real.log (ts / tg) := by
  have h := congrArg Real.log (normalized_powers ta tg ts hg law)
  rw [Real.log_pow, Real.log_pow] at h
  linarith only [h]

theorem full_period_intercept (ta tg ts : ℝ) (ha : 0 < ta) (hg : 0 < tg)
    (hs : 0 < ts) (law : ta ^ 3 = tg * ts ^ 2) :
    Real.log (ta / tg) =
      (2 / 3 : ℝ) * Real.log ((2 * Real.pi * ts) / tg) -
      (2 / 3 : ℝ) * Real.log (2 * Real.pi) := by
  rw [show (2 * Real.pi * ts) / tg = (2 * Real.pi) * (ts / tg) by ring,
      Real.log_mul (by positivity) (by positivity),
      logarithmic_slope ta tg ts ha hg hs law]
  ring

/-- End-to-end form using the one-radian time τS = (πab/(h/2))/(2π). -/
theorem ellipse_log_law (a b h μ c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hh : 0 < h) (hμ : 0 < μ) (hc : 0 < c)
    (hp : b ^ 2 / a = h ^ 2 / μ) :
    Real.log ((a / c) / (μ / c ^ 3)) =
      (2 / 3 : ℝ) * Real.log ((a * b / h) / (μ / c ^ 3)) := by
  have hq : b ^ 2 / h ^ 2 = a / μ := by
    apply (div_eq_div_iff (pow_ne_zero _ (ne_of_gt hh)) (ne_of_gt hμ)).2
    simpa [mul_comm] using (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hμ)).1 hp
  have hS : (a * b / h) ^ 2 = a ^ 3 / μ := by
    calc
      (a * b / h) ^ 2 = a ^ 2 * (b ^ 2 / h ^ 2) := by ring
      _ = a ^ 3 / μ := by rw [hq]; ring
  exact logarithmic_slope _ _ _ (div_pos ha hc) (by positivity) (by positivity)
    (light_time_law a μ c _ hc hμ hS)

theorem eightfold_time_fourfold_size (a₁ a₂ tg s₁ s₂ : ℝ)
    (h₁ : a₁ ^ 3 = tg * s₁ ^ 2) (h₂ : a₂ ^ 3 = tg * s₂ ^ 2)
    (ratio : s₂ = 8 * s₁) : a₂ = 4 * a₁ := by
  have cubes : a₂ ^ 3 = (4 * a₁) ^ 3 := by
    calc
      a₂ ^ 3 = tg * s₂ ^ 2 := h₂
      _ = 64 * (tg * s₁ ^ 2) := by rw [ratio]; ring
      _ = (4 * a₁) ^ 3 := by rw [← h₁]; ring
  exact (Odd.pow_injective (by decide : Odd (3 : ℕ))) cubes

end

#print axioms ellipse_period
#print axioms light_time_law
#print axioms normalized_powers
#print axioms logarithmic_slope
#print axioms full_period_intercept
#print axioms ellipse_log_law
#print axioms eightfold_time_fourfold_size

end KeplerLogarithms
