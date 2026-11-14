import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Manuscript 9 at 52f63595611ddfb987076dad328fef24735bb45d.
mu denotes the gravitational parameter GM. Newtonian Schuler frequency is a
model input, not a relativistic oscillator or a derivation of navigation physics.
-/
namespace MassTime
structure Parameters where
  mu : ℝ
  c : ℝ
  mu_pos : 0 < mu
  c_pos : 0 < c

noncomputable section
variable (P : Parameters)
def gravitationalTime := P.mu / P.c ^ 3
def radiusTime (R : ℝ) := R / P.c
def schwarzschildRadius := 2 * P.mu / P.c ^ 2
def compactness (R : ℝ) := P.mu / (R * P.c ^ 2)
def newtonianGravity (R : ℝ) := P.mu / R ^ 2
def gravityInverseTime (R : ℝ) := newtonianGravity P R / P.c
def schulerOmega (R : ℝ) := Real.sqrt (P.mu / R ^ 3)
def schulerTime (R : ℝ) := 1 / schulerOmega P R
def schulerFrequency (R : ℝ) := schulerOmega P R / (2 * Real.pi)
def schulerPeriod (R : ℝ) := 2 * Real.pi / schulerOmega P R

theorem gravitational_time_pos : 0 < gravitationalTime P :=
  div_pos P.mu_pos (pow_pos P.c_pos 3)
theorem radius_time_pos (R : ℝ) (hR : 0 < R) : 0 < radiusTime P R :=
  div_pos hR P.c_pos
theorem radius_from_time : schwarzschildRadius P = 2 * P.c * gravitationalTime P := by
  have hc := ne_of_gt P.c_pos
  unfold schwarzschildRadius gravitationalTime
  field_simp
  ring

theorem compactness_time (R : ℝ) (hR : 0 < R) :
    compactness P R = gravitationalTime P / radiusTime P R := by
  have hc := ne_of_gt P.c_pos
  have hr := ne_of_gt hR
  unfold compactness gravitationalTime radiusTime
  field_simp
  ring

theorem middle_scale (R : ℝ) (hR : 0 < R) :
    gravitationalTime P / radiusTime P R ^ 2 = gravityInverseTime P R := by
  have hc := ne_of_gt P.c_pos
  have hr := ne_of_gt hR
  unfold gravitationalTime radiusTime gravityInverseTime newtonianGravity
  field_simp
  ring

theorem schuler_omega_pos (R : ℝ) (hR : 0 < R) : 0 < schulerOmega P R :=
  Real.sqrt_pos.2 (div_pos P.mu_pos (pow_pos hR 3))
theorem schuler_time_pos (R : ℝ) (hR : 0 < R) : 0 < schulerTime P R :=
  div_pos zero_lt_one (schuler_omega_pos P R hR)

theorem schuler_square (R : ℝ) (hR : 0 < R) : schulerOmega P R ^ 2 = P.mu / R ^ 3 :=
  Real.sq_sqrt (le_of_lt (div_pos P.mu_pos (pow_pos hR 3)))

theorem schuler_gravity (R : ℝ) (hR : 0 < R) :
    schulerOmega P R ^ 2 = newtonianGravity P R / R := by
  rw [schuler_square P R hR]
  unfold newtonianGravity
  ring

theorem third_scale (R : ℝ) (hR : 0 < R) :
    schulerOmega P R ^ 2 = gravitationalTime P / radiusTime P R ^ 3 := by
  have hc := ne_of_gt P.c_pos
  have hr := ne_of_gt hR
  rw [schuler_square P R hR]
  unfold gravitationalTime radiusTime
  field_simp

theorem middle_from_schuler (R : ℝ) (hR : 0 < R) :
    gravityInverseTime P R = schulerOmega P R ^ 2 * radiusTime P R := by
  have hr := ne_of_gt hR
  have hc := ne_of_gt P.c_pos
  rw [schuler_square P R hR]
  unfold gravityInverseTime newtonianGravity radiusTime
  field_simp
  ring

theorem three_time_law (R : ℝ) (hR : 0 < R) :
    radiusTime P R ^ 3 = gravitationalTime P * schulerTime P R ^ 2 := by
  have hw := ne_of_gt (schuler_omega_pos P R hR)
  have ht := ne_of_gt (radius_time_pos P R hR)
  have heq := third_scale P R hR
  have hprod : schulerOmega P R ^ 2 * radiusTime P R ^ 3 = gravitationalTime P :=
    (eq_div_iff (pow_ne_zero 3 ht)).mp heq
  unfold schulerTime
  rw [div_pow, one_pow, one_div]
  apply (eq_div_iff (pow_ne_zero 2 hw)).2
  simpa [mul_comm] using hprod

theorem logarithmic_position (R : ℝ) (hR : 0 < R) :
    Real.log (radiusTime P R / gravitationalTime P) =
      (2 / 3 : ℝ) * Real.log (schulerTime P R / gravitationalTime P) := by
  have ht := ne_of_gt (radius_time_pos P R hR)
  have hg := ne_of_gt (gravitational_time_pos P)
  have hs := ne_of_gt (schuler_time_pos P R hR)
  have hl := congrArg Real.log (three_time_law P R hR)
  rw [Real.log_mul hg (pow_ne_zero 2 hs), Real.log_pow, Real.log_pow] at hl
  rw [Real.log_div ht hg, Real.log_div hs hg]
  norm_num at hl ⊢
  linarith

theorem period_from_one_radian (R : ℝ) :
    schulerPeriod P R = 2 * Real.pi * schulerTime P R := by
  unfold schulerPeriod schulerTime
  ring

theorem frequency_times_period (R : ℝ) (hR : 0 < R) :
    schulerFrequency P R * schulerPeriod P R = 1 := by
  have hw := ne_of_gt (schuler_omega_pos P R hR)
  have hp := ne_of_gt Real.pi_pos
  unfold schulerFrequency schulerPeriod
  field_simp

/-- First-order lag model only, not the exact Schwarzschild lag. -/
def firstOrderLag (R dt : ℝ) := compactness P R * dt
theorem first_order_lag_radius_time (R : ℝ) (hR : 0 < R) :
    firstOrderLag P R (radiusTime P R) = gravitationalTime P := by
  have ht := ne_of_gt (radius_time_pos P R hR)
  unfold firstOrderLag
  rw [compactness_time P R hR]
  exact div_mul_cancel₀ _ ht

#print axioms gravitational_time_pos
#print axioms radius_time_pos
#print axioms radius_from_time
#print axioms compactness_time
#print axioms middle_scale
#print axioms schuler_omega_pos
#print axioms schuler_time_pos
#print axioms schuler_square
#print axioms schuler_gravity
#print axioms third_scale
#print axioms middle_from_schuler
#print axioms three_time_law
#print axioms logarithmic_position
#print axioms period_from_one_radian
#print axioms frequency_times_period
#print axioms first_order_lag_radius_time
end
end MassTime
