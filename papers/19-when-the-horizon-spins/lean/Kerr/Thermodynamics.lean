import Kerr.Extraction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Kerr
structure Parameters where
  G : ℝ
  M : ℝ
  c : ℝ
  hbar : ℝ
  kB : ℝ
  J : ℝ
  G_pos : 0 < G
  M_pos : 0 < M
  c_pos : 0 < c
  hbar_pos : 0 < hbar
  kB_pos : 0 < kB

noncomputable section
variable (P : Parameters)
def tauG := P.G * P.M / P.c ^ 3
def tauJ := P.J / (P.M * P.c ^ 2)
def chi := tauJ P / tauG P
def totalEnergy := P.M * P.c ^ 2
def planckArea := P.hbar * P.G / P.c ^ 3
/-- Supplied Kerr angular-velocity formula in coordinate-radius/time variables. -/
def omega := tauJ P / (outer (tauG P) (chi P) ^ 2 + tauJ P ^ 2)
/-- Supplied surface gravity; its extremal value is an algebraic extension. -/
def surfaceGravity := P.c * (outer (tauG P) (chi P) - inner (tauG P) (chi P)) /
  (2 * (outer (tauG P) (chi P) ^ 2 + tauJ P ^ 2))
/-- Supplied Kerr area formula, using r=c*tau and a=c*tauJ. -/
def area := 4 * Real.pi * P.c ^ 2 * (outer (tauG P) (chi P) ^ 2 + tauJ P ^ 2)
/-- Standard semiclassical Hawking temperature is a model input. -/
def temperature := P.hbar * surfaceGravity P / (2 * Real.pi * P.c * P.kB)
/-- Bekenstein-Hawking area law is a model input. -/
def entropy := P.kB * area P / (4 * planckArea P)
def schwarzschildTemperature := P.hbar / (8 * Real.pi * P.kB * tauG P)
def formalEnergy := P.hbar / (2 * tauG P)

theorem tauG_pos : 0 < tauG P := by
  exact div_pos (mul_pos P.G_pos P.M_pos) (pow_pos P.c_pos 3)
theorem energy_pos : 0 < totalEnergy P := by
  exact mul_pos P.M_pos (pow_pos P.c_pos 2)
theorem planckArea_pos : 0 < planckArea P := by
  exact div_pos (mul_pos P.hbar_pos P.G_pos) (pow_pos P.c_pos 3)

theorem spin_formula : chi P = P.c * P.J / (P.G * P.M ^ 2) := by
  have hg := ne_of_gt P.G_pos
  have hm := ne_of_gt P.M_pos
  have hc := ne_of_gt P.c_pos
  unfold chi tauJ tauG
  field_simp
  ring

theorem spin_time_relation : tauJ P = tauG P * chi P := by
  unfold chi
  field_simp [ne_of_gt (tauG_pos P)]

theorem angular_momentum_relation : P.J = tauJ P * totalEnergy P := by
  have hm := ne_of_gt P.M_pos
  have hc := ne_of_gt P.c_pos
  unfold tauJ totalEnergy
  field_simp

theorem planck_area_time_relation : planckArea P = P.hbar * tauG P / P.M := by
  have hm := ne_of_gt P.M_pos
  have hc := ne_of_gt P.c_pos
  unfold planckArea tauG
  field_simp
  ring

theorem denominator_pos : 0 < outer (tauG P) (chi P) ^ 2 + tauJ P ^ 2 := by
  have hp := outer_pos (tauG_pos P) (x := chi P)
  nlinarith [sq_nonneg (tauJ P)]

theorem denominator_form (h : |chi P| ≤ 1) :
    outer (tauG P) (chi P) ^ 2 + tauJ P ^ 2 =
      2 * tauG P ^ 2 * (1 + sigma (chi P)) := by
  rw [spin_time_relation P]
  exact horizon_denominator h

theorem omega_form (h : |chi P| ≤ 1) :
    omega P = chi P / (2 * tauG P * (1 + sigma (chi P))) := by
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  unfold omega
  rw [denominator_form P h, spin_time_relation P]
  field_simp
  ring

theorem omega_sign : 0 < omega P ↔ 0 < P.J := by
  unfold omega
  rw [div_pos_iff_of_pos_right (denominator_pos P)]
  unfold tauJ
  exact div_pos_iff_of_pos_right (mul_pos P.M_pos (sq_pos_of_pos P.c_pos))

theorem surface_gravity_form (h : |chi P| ≤ 1) :
    surfaceGravity P = P.c * sigma (chi P) / (2 * tauG P * (1 + sigma (chi P))) := by
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  unfold surfaceGravity
  rw [denominator_form P h]
  unfold outer inner
  field_simp
  ring

theorem area_form (h : |chi P| ≤ 1) :
    area P = 8 * Real.pi * P.c ^ 2 * tauG P ^ 2 * (1 + sigma (chi P)) := by
  unfold area
  rw [denominator_form P h]
  ring

theorem temperature_form (h : |chi P| ≤ 1) :
    temperature P = P.hbar * sigma (chi P) /
      (4 * Real.pi * P.kB * tauG P * (1 + sigma (chi P))) := by
  have hc := ne_of_gt P.c_pos
  have hk := ne_of_gt P.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  unfold temperature
  rw [surface_gravity_form P h]
  field_simp
  ring

theorem temperature_ratio (h : |chi P| ≤ 1) :
    temperature P / schwarzschildTemperature P = 2 * sigma (chi P) / (1 + sigma (chi P)) := by
  have hh := ne_of_gt P.hbar_pos
  have hk := ne_of_gt P.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  rw [temperature_form P h]
  unfold schwarzschildTemperature
  field_simp
  ring

theorem thermal_smarr_fraction (h : |chi P| ≤ 1) :
    2 * temperature P * entropy P / totalEnergy P = sigma (chi P) := by
  have hm := ne_of_gt P.M_pos
  have hc := ne_of_gt P.c_pos
  have hh := ne_of_gt P.hbar_pos
  have hk := ne_of_gt P.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  unfold entropy
  rw [temperature_form P h, area_form P h, planck_area_time_relation P]
  unfold totalEnergy
  field_simp
  ring

theorem rotational_smarr_fraction (h : |chi P| ≤ 1) :
    2 * omega P * P.J / totalEnergy P = 1 - sigma (chi P) := by
  have he := ne_of_gt (energy_pos P)
  have ht := ne_of_gt (tauG_pos P)
  have hs : 1 + sigma (chi P) ≠ 0 := by linarith [sigma_nonneg (chi P)]
  rw [omega_form P h, angular_momentum_relation P, spin_time_relation P]
  field_simp
  nlinarith [congrArg (fun z : ℝ => tauG P * totalEnergy P * z) (sigma_sq h)]

theorem smarr_identity (h : |chi P| ≤ 1) :
    totalEnergy P = 2 * temperature P * entropy P + 2 * omega P * P.J := by
  have ht := (div_eq_iff (ne_of_gt (energy_pos P))).1 (thermal_smarr_fraction P h)
  have hr := (div_eq_iff (ne_of_gt (energy_pos P))).1 (rotational_smarr_fraction P h)
  nlinarith

theorem temperature_pos (h : |chi P| < 1) : 0 < temperature P := by
  rw [temperature_form P (le_of_lt h)]
  have hs := sigma_pos h
  have ht := tauG_pos P
  have hh := P.hbar_pos
  have hk := P.kB_pos
  positivity

theorem extremal_temperature (h : |chi P| = 1) : temperature P = 0 := by
  rw [temperature_form P (le_of_eq h), sigma_extremal h]
  simp

theorem formal_thermal_ratio (h : |chi P| < 1) :
    formalEnergy P / (P.kB * temperature P) =
      2 * Real.pi * (1 + sigma (chi P)) / sigma (chi P) := by
  have hh := ne_of_gt P.hbar_pos
  have hk := ne_of_gt P.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have ht := ne_of_gt (tauG_pos P)
  have hs := ne_of_gt (sigma_pos h)
  unfold formalEnergy
  rw [temperature_form P (le_of_lt h)]
  field_simp
  ring

theorem irreducible_mass_square :
    (P.M * irreducibleRatio (chi P)) ^ 2 = P.M ^ 2 * (1 + sigma (chi P)) / 2 := by
  rw [mul_pow, irreducible_ratio_sq]
  ring

theorem irreducible_mass_area (h : |chi P| ≤ 1) :
    area P = 16 * Real.pi * P.G ^ 2 * (P.M * irreducibleRatio (chi P)) ^ 2 / P.c ^ 4 := by
  have hc := ne_of_gt P.c_pos
  rw [area_form P h, irreducible_mass_square]
  unfold tauG
  field_simp
  ring

theorem area_smarr_link (h : |chi P| ≤ 1) :
    totalEnergy P - 2 * omega P * P.J = (1 / 2 : ℝ) * (area P / planckArea P) * P.kB * temperature P := by
  rw [smarr_identity P h]
  unfold entropy
  ring


theorem zero_spin_omega (h : chi P = 0) : omega P = 0 := by
  have hb : |chi P| ≤ 1 := by rw [h]; norm_num
  rw [omega_form P hb, h]
  simp

theorem extremal_omega_abs (h : |chi P| = 1) : |omega P| = 1 / (2 * tauG P) := by
  rw [omega_form P (le_of_eq h), sigma_extremal h]
  have ht := tauG_pos P
  simp [abs_div, abs_mul, h, abs_of_pos ht]

#print axioms tauG_pos
#print axioms energy_pos
#print axioms planckArea_pos
#print axioms spin_formula
#print axioms spin_time_relation
#print axioms angular_momentum_relation
#print axioms planck_area_time_relation
#print axioms denominator_pos
#print axioms denominator_form
#print axioms omega_form
#print axioms omega_sign
#print axioms surface_gravity_form
#print axioms area_form
#print axioms temperature_form
#print axioms temperature_ratio
#print axioms thermal_smarr_fraction
#print axioms rotational_smarr_fraction
#print axioms smarr_identity
#print axioms temperature_pos
#print axioms extremal_temperature
#print axioms formal_thermal_ratio
#print axioms irreducible_mass_square
#print axioms irreducible_mass_area
#print axioms area_smarr_link
#print axioms zero_spin_omega
#print axioms extremal_omega_abs
end
end Kerr
