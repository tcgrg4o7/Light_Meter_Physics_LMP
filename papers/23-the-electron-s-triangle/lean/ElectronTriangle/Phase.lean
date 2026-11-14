import ElectronTriangle.Kinematics

namespace ElectronTriangle
noncomputable section
variable (P : Parameters)
def planckConstant := 2 * Real.pi * P.hbar
def comptonFrequency := restEnergy P / planckConstant P
def comptonWavelength := planckConstant P / (P.m * P.c)
def phase (x t : ℝ) := (momentum P * x - energy P * t) / P.hbar

theorem compton_period : 1 / comptonFrequency P = comptonWavelength P / P.c := by
  have hm := ne_of_gt P.m_pos
  have hc := ne_of_gt P.c_pos
  have hp : planckConstant P ≠ 0 := ne_of_gt (mul_pos (mul_pos (by norm_num) Real.pi_pos) P.hbar_pos)
  unfold comptonFrequency comptonWavelength restEnergy
  field_simp
  ring_nf
  simp
theorem lab_frequency : energy P / planckConstant P = (5 / 3 : ℝ) * comptonFrequency P := by
  rw [energy_value]
  unfold comptonFrequency restEnergy
  ring
theorem lab_wavelength : planckConstant P / momentum P = (3 / 4 : ℝ) * comptonWavelength P := by
  rw [momentum_value]
  unfold comptonWavelength
  ring
theorem phase_angle (x t : ℝ) : phase P x t =
    2 * Real.pi * comptonFrequency P * (4 * x / (3 * P.c) - 5 * t / 3) := by
  have hc := ne_of_gt P.c_pos
  have hh := ne_of_gt P.hbar_pos
  have hp := ne_of_gt Real.pi_pos
  unfold phase comptonFrequency planckConstant restEnergy
  rw [momentum_value, energy_value]
  field_simp
  ring

theorem fixed_phase_derivative (x t : ℝ) :
    HasDerivAt (fun s => phase P x s) (-energy P / P.hbar) t := by
  simpa [phase] using (((hasDerivAt_const t (momentum P * x)).sub
    ((hasDerivAt_id t).const_mul (energy P))).div_const P.hbar)
theorem path_phase_derivative (t : ℝ) :
    HasDerivAt (fun s => phase P (velocity P * s) s)
      (-(3 / 5 : ℝ) * restEnergy P / P.hbar) t := by
  have hf : (fun s => phase P (velocity P * s) s) =
      fun s => (-(3 / 5 : ℝ) * restEnergy P / P.hbar) * s := by
    funext s
    unfold phase
    rw [action_on_worldline, proper_time_value]
    ring
  rw [hf]
  simpa using (hasDerivAt_id t).const_mul (-(3 / 5 : ℝ) * restEnergy P / P.hbar)
theorem proper_phase_derivative (tau : ℝ) :
    HasDerivAt (fun s => phase P (velocity P * (gamma * s)) (gamma * s))
      (-restEnergy P / P.hbar) tau := by
  have hf : (fun s => phase P (velocity P * (gamma * s)) (gamma * s)) =
      fun s => (-restEnergy P / P.hbar) * s := by
    funext s
    unfold phase
    rw [action_on_worldline, proper_time_value, gamma_value]
    ring
  rw [hf]
  simpa using (hasDerivAt_id tau).const_mul (-restEnergy P / P.hbar)

theorem fixed_phase_rate (x t : ℝ) :
    -(1 / (2 * Real.pi)) * deriv (fun s => phase P x s) t =
      (5 / 3 : ℝ) * comptonFrequency P := by
  rw [(fixed_phase_derivative P x t).deriv, energy_value]
  unfold comptonFrequency restEnergy planckConstant
  ring
theorem path_phase_rate (t : ℝ) :
    -(1 / (2 * Real.pi)) * deriv (fun s => phase P (velocity P * s) s) t =
      (3 / 5 : ℝ) * comptonFrequency P := by
  rw [(path_phase_derivative P t).deriv]
  unfold comptonFrequency planckConstant
  ring
theorem proper_phase_rate (tau : ℝ) :
    -(1 / (2 * Real.pi)) * deriv (fun s => phase P (velocity P * (gamma * s)) (gamma * s)) tau =
      comptonFrequency P := by
  rw [(proper_phase_derivative P tau).deriv]
  unfold comptonFrequency planckConstant
  ring

#print axioms compton_period
#print axioms lab_frequency
#print axioms lab_wavelength
#print axioms phase_angle
#print axioms fixed_phase_derivative
#print axioms path_phase_derivative
#print axioms proper_phase_derivative
#print axioms fixed_phase_rate
#print axioms path_phase_rate
#print axioms proper_phase_rate
end
end ElectronTriangle
