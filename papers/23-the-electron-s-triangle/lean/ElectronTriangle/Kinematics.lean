import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ElectronTriangle
structure Parameters where
  m : ℝ
  c : ℝ
  hbar : ℝ
  m_pos : 0 < m
  c_pos : 0 < c
  hbar_pos : 0 < hbar

noncomputable section
variable (P : Parameters)
def beta : ℝ := 4 / 5
def gamma : ℝ := 1 / Real.sqrt (1 - beta ^ 2)
def velocity := beta * P.c
def restEnergy := P.m * P.c ^ 2
def energy := gamma * restEnergy P
def momentum := gamma * P.m * velocity P
def kinetic := energy P - restEnergy P
def properTime (t : ℝ) := t / gamma
def lorentzTime (x t : ℝ) := gamma * (t - velocity P * x / P.c ^ 2)
def lagrangian (v : ℝ) := -P.m * P.c ^ 2 * Real.sqrt (1 - v ^ 2 / P.c ^ 2)
def dispersion (p : ℝ) := Real.sqrt (p ^ 2 * P.c ^ 2 + P.m ^ 2 * P.c ^ 4)

theorem beta_sqrt : Real.sqrt (1 - beta ^ 2) = (3 / 5 : ℝ) := by
  unfold beta
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num
theorem gamma_value : gamma = (5 / 3 : ℝ) := by
  unfold gamma
  rw [beta_sqrt]
  norm_num
theorem velocity_value : velocity P = (4 / 5 : ℝ) * P.c := rfl
theorem energy_value : energy P = (5 / 3 : ℝ) * P.m * P.c ^ 2 := by
  unfold energy restEnergy
  rw [gamma_value]
  ring
theorem momentum_value : momentum P = (4 / 3 : ℝ) * P.m * P.c := by
  unfold momentum velocity beta
  rw [gamma_value]
  ring
theorem energy_pos : 0 < energy P := by
  rw [energy_value]
  exact mul_pos (mul_pos (by norm_num) P.m_pos) (sq_pos_of_pos P.c_pos)
theorem momentum_pos : 0 < momentum P := by
  rw [momentum_value]
  exact mul_pos (mul_pos (by norm_num) P.m_pos) P.c_pos
theorem proper_time_value (t : ℝ) : properTime t = (3 / 5 : ℝ) * t := by
  unfold properTime
  rw [gamma_value]
  ring
theorem mass_shell : energy P ^ 2 = (momentum P * P.c) ^ 2 + restEnergy P ^ 2 := by
  rw [energy_value, momentum_value]
  unfold restEnergy
  ring
theorem triangle_ratios :
    energy P / (restEnergy P / 3) = 5 ∧
    (momentum P * P.c) / (restEnergy P / 3) = 4 ∧
    restEnergy P / (restEnergy P / 3) = 3 := by
  have hm := ne_of_gt P.m_pos
  have hc := ne_of_gt P.c_pos
  rw [energy_value, momentum_value]
  unfold restEnergy
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    ring
  · field_simp
theorem kinetic_value : kinetic P = (2 / 3 : ℝ) * restEnergy P := by
  unfold kinetic restEnergy
  rw [energy_value]
  ring
theorem lightcone_values :
    energy P + momentum P * P.c = 3 * restEnergy P ∧
    energy P - momentum P * P.c = restEnergy P / 3 := by
  rw [energy_value, momentum_value]
  unfold restEnergy
  constructor <;> ring
theorem lightcone_product :
    (energy P + momentum P * P.c) * (energy P - momentum P * P.c) = restEnergy P ^ 2 := by
  rw [(lightcone_values P).1, (lightcone_values P).2]
  ring

theorem selected_radicand : 1 - velocity P ^ 2 / P.c ^ 2 = (9 / 25 : ℝ) := by
  have hc := ne_of_gt P.c_pos
  unfold velocity beta
  field_simp
  ring
theorem selected_sqrt : Real.sqrt (1 - velocity P ^ 2 / P.c ^ 2) = (3 / 5 : ℝ) := by
  rw [selected_radicand]
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

/-- Canonical momentum from the supplied free-particle Lagrangian at v=4c/5. -/
theorem lagrangian_derivative : HasDerivAt (lagrangian P) (momentum P) (velocity P) := by
  have hc := ne_of_gt P.c_pos
  have hr : 1 - velocity P ^ 2 / P.c ^ 2 ≠ 0 := by rw [selected_radicand]; norm_num
  have hd := (((hasDerivAt_id (velocity P)).pow 2).div_const (P.c ^ 2)).const_sub 1
  have hs := (hd.sqrt hr).const_mul (-P.m * P.c ^ 2)
  convert hs using 1
  simp only [id_eq]
  rw [selected_sqrt, momentum_value]
  unfold velocity beta
  field_simp
  ring

theorem lagrangian_value : lagrangian P (velocity P) = -(3 / 5 : ℝ) * restEnergy P := by
  unfold lagrangian
  rw [selected_sqrt]
  unfold restEnergy
  ring
theorem legendre_energy : momentum P * velocity P - lagrangian P (velocity P) = energy P := by
  rw [lagrangian_value, momentum_value, energy_value]
  unfold velocity beta restEnergy
  ring

theorem boosted_phase_action (x t : ℝ) :
    -restEnergy P * lorentzTime P x t = momentum P * x - energy P * t := by
  have hc := ne_of_gt P.c_pos
  unfold lorentzTime restEnergy
  rw [momentum_value, energy_value, gamma_value]
  unfold velocity beta
  field_simp
  ring
theorem lorentz_time_on_worldline (t : ℝ) : lorentzTime P (velocity P * t) t = properTime t := by
  have hc := ne_of_gt P.c_pos
  unfold lorentzTime properTime velocity beta
  rw [gamma_value]
  field_simp
  ring
theorem action_on_worldline (t : ℝ) :
    momentum P * (velocity P * t) - energy P * t = -restEnergy P * properTime t := by
  rw [← boosted_phase_action, lorentz_time_on_worldline]

theorem celerity_value : momentum P / P.m = (4 / 3 : ℝ) * P.c := by
  have hm := ne_of_gt P.m_pos
  rw [momentum_value]
  field_simp
  ring
theorem phase_velocity_value : energy P / momentum P = (5 / 4 : ℝ) * P.c := by
  have hm := ne_of_gt P.m_pos
  have hc := ne_of_gt P.c_pos
  rw [energy_value, momentum_value]
  field_simp
  ring
theorem group_slope_value : momentum P * P.c ^ 2 / energy P = velocity P := by
  have hm := ne_of_gt P.m_pos
  have hc := ne_of_gt P.c_pos
  rw [energy_value, momentum_value]
  unfold velocity beta
  field_simp
  ring
theorem dispersion_at_momentum : dispersion P (momentum P) = energy P := by
  have he := mass_shell P
  have hrad : momentum P ^ 2 * P.c ^ 2 + P.m ^ 2 * P.c ^ 4 = energy P ^ 2 := by
    unfold restEnergy at he
    nlinarith [he]
  unfold dispersion
  rw [hrad, Real.sqrt_sq (le_of_lt (energy_pos P))]
theorem dispersion_derivative : HasDerivAt (dispersion P) (velocity P) (momentum P) := by
  have hp := ne_of_gt (energy_pos P)
  have hrad : momentum P ^ 2 * P.c ^ 2 + P.m ^ 2 * P.c ^ 4 ≠ 0 := by
    have : 0 < momentum P ^ 2 * P.c ^ 2 + P.m ^ 2 * P.c ^ 4 := by
      have hm := P.m_pos
      have hc := P.c_pos
      positivity
    exact ne_of_gt this
  have hd := ((((hasDerivAt_id (momentum P)).pow 2).mul_const (P.c ^ 2)).add_const
    (P.m ^ 2 * P.c ^ 4)).sqrt hrad
  convert hd using 1
  change velocity P = (2 * momentum P ^ (2 - 1) * 1 * P.c ^ 2) / (2 * dispersion P (momentum P))
  rw [dispersion_at_momentum, ← group_slope_value]
  simp
  ring

theorem nonrel_kinetic_value : momentum P ^ 2 / (2 * P.m) = (8 / 9 : ℝ) * restEnergy P := by
  have hm := ne_of_gt P.m_pos
  rw [momentum_value]
  unfold restEnergy
  field_simp
  ring
theorem nonrel_kinetic_ratio : (momentum P ^ 2 / (2 * P.m)) / kinetic P = (4 / 3 : ℝ) := by
  have hm := ne_of_gt P.m_pos
  have hc := ne_of_gt P.c_pos
  rw [nonrel_kinetic_value, kinetic_value]
  unfold restEnergy
  field_simp
  ring

#print axioms beta_sqrt
#print axioms gamma_value
#print axioms velocity_value
#print axioms energy_value
#print axioms momentum_value
#print axioms energy_pos
#print axioms momentum_pos
#print axioms proper_time_value
#print axioms mass_shell
#print axioms triangle_ratios
#print axioms kinetic_value
#print axioms lightcone_values
#print axioms lightcone_product
#print axioms selected_radicand
#print axioms selected_sqrt
#print axioms lagrangian_derivative
#print axioms lagrangian_value
#print axioms legendre_energy
#print axioms boosted_phase_action
#print axioms lorentz_time_on_worldline
#print axioms action_on_worldline
#print axioms celerity_value
#print axioms phase_velocity_value
#print axioms group_slope_value
#print axioms dispersion_at_momentum
#print axioms dispersion_derivative
#print axioms nonrel_kinetic_value
#print axioms nonrel_kinetic_ratio
end
end ElectronTriangle
