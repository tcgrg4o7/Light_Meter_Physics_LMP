import ElectronTriangle.Phase
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

namespace ElectronTriangle
noncomputable section
variable (P : Parameters)
def spatialCoefficient : ℂ := Complex.I * (momentum P : ℂ) / (P.hbar : ℂ)
def temporalCoefficient : ℂ := -Complex.I * (energy P : ℂ) / (P.hbar : ℂ)
def wave (A : ℂ) (x t : ℝ) : ℂ :=
  A * Complex.exp (spatialCoefficient P * (x : ℂ) + temporalCoefficient P * (t : ℂ))

theorem wave_phase_convention (A : ℂ) (x t : ℝ) :
    wave P A x t = A * Complex.exp (Complex.I * (phase P x t : ℂ)) := by
  unfold wave spatialCoefficient temporalCoefficient phase
  apply congrArg (fun z : ℂ => A * Complex.exp z)
  push_cast
  ring

theorem affine_exponential_derivative (A a b : ℂ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => A * Complex.exp (a * (x : ℂ) + b))
      (a * (A * Complex.exp (a * (s : ℂ) + b))) s := by
  have hd := (((hasDerivAt_id (s : ℂ)).const_mul a).add_const b).cexp
  simpa [mul_assoc, mul_comm, mul_left_comm] using (hd.const_mul A).comp_ofReal

theorem wave_spatial_derivative (A : ℂ) (x t : ℝ) :
    HasDerivAt (fun y : ℝ => wave P A y t) (spatialCoefficient P * wave P A x t) x := by
  exact affine_exponential_derivative A (spatialCoefficient P) (temporalCoefficient P * (t : ℂ)) x

theorem wave_temporal_derivative (A : ℂ) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => wave P A x s) (temporalCoefficient P * wave P A x t) t := by
  simpa [wave, add_comm] using
    affine_exponential_derivative A (temporalCoefficient P) (spatialCoefficient P * (x : ℂ)) t

theorem wave_spatial_second_derivative (A : ℂ) (x t : ℝ) :
    deriv (fun y : ℝ => deriv (fun z : ℝ => wave P A z t) y) x =
      spatialCoefficient P ^ 2 * wave P A x t := by
  have hf : (fun y : ℝ => deriv (fun z : ℝ => wave P A z t) y) =
      fun y => spatialCoefficient P * wave P A y t := by
    funext y
    exact (wave_spatial_derivative P A y t).deriv
  rw [hf, ((wave_spatial_derivative P A x t).const_mul (spatialCoefficient P)).deriv]
  ring

theorem wave_temporal_second_derivative (A : ℂ) (x t : ℝ) :
    deriv (fun s : ℝ => deriv (fun u : ℝ => wave P A x u) s) t =
      temporalCoefficient P ^ 2 * wave P A x t := by
  have hf : (fun s : ℝ => deriv (fun u : ℝ => wave P A x u) s) =
      fun s => temporalCoefficient P * wave P A x s := by
    funext s
    exact (wave_temporal_derivative P A x s).deriv
  rw [hf, ((wave_temporal_derivative P A x t).const_mul (temporalCoefficient P)).deriv]
  ring

theorem momentum_operator_eigenvalue (A : ℂ) (x t : ℝ) :
    (-Complex.I * (P.hbar : ℂ)) * deriv (fun y : ℝ => wave P A y t) x =
      (momentum P : ℂ) * wave P A x t := by
  have hh : (P.hbar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt P.hbar_pos
  rw [(wave_spatial_derivative P A x t).deriv]
  unfold spatialCoefficient
  field_simp
  ring_nf
  simp [Complex.I_sq]

theorem energy_operator_eigenvalue (A : ℂ) (x t : ℝ) :
    (Complex.I * (P.hbar : ℂ)) * deriv (fun s : ℝ => wave P A x s) t =
      (energy P : ℂ) * wave P A x t := by
  have hh : (P.hbar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt P.hbar_pos
  rw [(wave_temporal_derivative P A x t).deriv]
  unfold temporalCoefficient
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- Actual complex-valued 1+1 dimensional KG residual, not just its scalar coefficient. -/
theorem klein_gordon_plane_wave (A : ℂ) (x t : ℝ) :
    (1 / (P.c : ℂ) ^ 2) * deriv (fun s : ℝ => deriv (fun u : ℝ => wave P A x u) s) t -
      deriv (fun y : ℝ => deriv (fun z : ℝ => wave P A z t) y) x +
      (((P.m : ℂ) * (P.c : ℂ)) / (P.hbar : ℂ)) ^ 2 * wave P A x t = 0 := by
  have hh : (P.hbar : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt P.hbar_pos
  have hc : (P.c : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt P.c_pos
  rw [wave_spatial_second_derivative, wave_temporal_second_derivative]
  unfold spatialCoefficient temporalCoefficient
  rw [energy_value, momentum_value]
  push_cast
  field_simp
  ring_nf
  simp [Complex.I_sq]

#print axioms wave_phase_convention
#print axioms affine_exponential_derivative
#print axioms wave_spatial_derivative
#print axioms wave_temporal_derivative
#print axioms wave_spatial_second_derivative
#print axioms wave_temporal_second_derivative
#print axioms momentum_operator_eigenvalue
#print axioms energy_operator_eigenvalue
#print axioms klein_gordon_plane_wave
end
end ElectronTriangle
