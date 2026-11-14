import MassTime.Scales
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace MassTime
noncomputable section
variable (P : Parameters)

def lapse (R : ℝ) := Real.sqrt (1 - schwarzschildRadius P / R)
def inverseRate (R : ℝ) := 1 / lapse P R
def inverseRateExcess (R : ℝ) := inverseRate P R - 1

theorem exterior_radicand_pos (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) : 0 < 1 - schwarzschildRadius P / R := by
  have h := (div_lt_one hR).2 hext
  linarith

theorem lapse_pos (R : ℝ) (hR : 0 < R) (hext : schwarzschildRadius P < R) :
    0 < lapse P R := Real.sqrt_pos.2 (exterior_radicand_pos P R hR hext)

theorem inverse_rate_pos (R : ℝ) (hR : 0 < R) (hext : schwarzschildRadius P < R) :
    0 < inverseRate P R := div_pos zero_lt_one (lapse_pos P R hR hext)

theorem radius_ratio_compactness (R : ℝ) :
    schwarzschildRadius P / R = 2 * compactness P R := by
  unfold schwarzschildRadius compactness
  ring

theorem exact_inverse_rate (R : ℝ) (hR : 0 < R)
    (_hext : schwarzschildRadius P < R) :
    inverseRate P R = 1 / Real.sqrt (1 - 2 * gravitationalTime P / radiusTime P R) := by
  unfold inverseRate lapse
  rw [radius_ratio_compactness, compactness_time P R hR]
  congr 3
  ring

theorem horizon_time_equivalence (R : ℝ) :
    R = schwarzschildRadius P ↔ radiusTime P R = 2 * gravitationalTime P := by
  have hc := ne_of_gt P.c_pos
  unfold radiusTime
  rw [div_eq_iff hc, radius_from_time]
  constructor <;> intro h <;> nlinarith [h]

theorem exact_inverse_excess (R : ℝ) (_hR : 0 < R)
    (_hext : schwarzschildRadius P < R) :
    inverseRateExcess P R = 1 / Real.sqrt (1 - 2 * compactness P R) - 1 := by
  unfold inverseRateExcess inverseRate lapse
  rw [radius_ratio_compactness]

/-- A derivative at zero checks the first-order coefficient, not a finite error bound. -/
theorem weak_excess_first_derivative :
    HasDerivAt (fun x : ℝ => 1 / Real.sqrt (1 - 2 * x) - 1) 1 0 := by
  have hd : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_sub 1
  have hs := hd.sqrt (by norm_num : (1 : ℝ) - 2 * 0 ≠ 0)
  have hi := hs.inv (by norm_num : Real.sqrt ((1 : ℝ) - 2 * 0) ≠ 0)
  simpa [one_div] using hi.sub (hasDerivAt_const (0 : ℝ) 1)

theorem radial_radicand_derivative (R : ℝ) (hR : 0 < R) :
    HasDerivAt (fun r : ℝ => 1 - schwarzschildRadius P / r)
      (schwarzschildRadius P / R ^ 2) R := by
  have hr := ne_of_gt hR
  simpa [neg_div] using ((hasDerivAt_const R (schwarzschildRadius P)).div (hasDerivAt_id R) hr).const_sub 1

theorem inverse_rate_derivative (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) :
    HasDerivAt (inverseRate P) (-schwarzschildRadius P / (2 * R ^ 2 * lapse P R ^ 3)) R := by
  have hs := ne_of_gt (lapse_pos P R hR hext)
  have hr := ne_of_gt hR
  have hd := (radial_radicand_derivative P R hR).sqrt (ne_of_gt (exterior_radicand_pos P R hR hext))
  have hi := hd.inv hs
  change HasDerivAt (fun r => (lapse P r)⁻¹) _ R at hi
  have hfun : inverseRate P = fun r => (lapse P r)⁻¹ := by
    funext r
    exact one_div (lapse P r)
  rw [hfun]
  convert hi using 1
  change -schwarzschildRadius P / (2 * R ^ 2 * lapse P R ^ 3) =
    -(schwarzschildRadius P / R ^ 2 / (2 * lapse P R)) / lapse P R ^ 2
  field_simp
  ring
  simp

theorem log_inverse_rate_derivative (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) :
    HasDerivAt (fun r => Real.log (inverseRate P r))
      (-schwarzschildRadius P / (2 * R ^ 2 * lapse P R ^ 2)) R := by
  have hs := ne_of_gt (lapse_pos P R hR hext)
  have hr := ne_of_gt hR
  have hd := (inverse_rate_derivative P R hR hext).log (ne_of_gt (inverse_rate_pos P R hR hext))
  convert hd using 1
  unfold inverseRate
  field_simp
  ring

/-- Outward coefficient of proper-radial gradient: dL=dr/alpha, hence alpha*d/dr. -/
def properRadialGradient (F : ℝ → ℝ) (R : ℝ) := lapse P R * deriv F R

theorem exact_proper_gradient (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) :
    P.c ^ 2 * properRadialGradient P (fun r => Real.log (inverseRate P r)) R =
      -P.mu / (R ^ 2 * lapse P R) := by
  have hs := ne_of_gt (lapse_pos P R hR hext)
  have hr := ne_of_gt hR
  have hc := ne_of_gt P.c_pos
  unfold properRadialGradient
  rw [(log_inverse_rate_derivative P R hR hext).deriv]
  unfold schwarzschildRadius
  field_simp
  ring

theorem exact_proper_gradient_inward (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) :
    P.c ^ 2 * properRadialGradient P (fun r => Real.log (inverseRate P r)) R < 0 := by
  rw [exact_proper_gradient P R hR hext]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos P.mu_pos)
    (mul_pos (sq_pos_of_pos hR) (lapse_pos P R hR hext))

/-- Exact inverse-time magnitude includes 1/alpha; f_g alone is the weak-field scale. -/
theorem proper_gradient_inverse_time (R : ℝ) (hR : 0 < R)
    (hext : schwarzschildRadius P < R) :
    -(P.c ^ 2 * properRadialGradient P (fun r => Real.log (inverseRate P r)) R) / P.c =
      gravityInverseTime P R / lapse P R := by
  rw [exact_proper_gradient P R hR hext]
  unfold gravityInverseTime newtonianGravity
  ring

#print axioms exterior_radicand_pos
#print axioms lapse_pos
#print axioms inverse_rate_pos
#print axioms radius_ratio_compactness
#print axioms exact_inverse_rate
#print axioms horizon_time_equivalence
#print axioms exact_inverse_excess
#print axioms weak_excess_first_derivative
#print axioms radial_radicand_derivative
#print axioms inverse_rate_derivative
#print axioms log_inverse_rate_derivative
#print axioms exact_proper_gradient
#print axioms exact_proper_gradient_inward
#print axioms proper_gradient_inverse_time
end
end MassTime
