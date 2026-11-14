import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
Manuscript 16, source commit 219958afcf921b669f07b9b5631520a22d2d5fb4.
Model inputs are explicit definitions: Schwarzschild radius, spherical area,
Planck area, Bekenstein-Hawking area entropy, and Hawking temperature at infinity.
These definitions encode physical laws; this file does not derive them from
Einstein's equations or quantum field theory. Real scalars use consistent units.
-/
namespace SmarrPilot

structure Constants where
  G : ℝ
  c : ℝ
  hbar : ℝ
  kB : ℝ
  G_pos : 0 < G
  c_pos : 0 < c
  hbar_pos : 0 < hbar
  kB_pos : 0 < kB

noncomputable section
variable (K : Constants)

def radius (M : ℝ) := 2 * K.G * M / K.c ^ 2
def gravitationalTime (M : ℝ) := K.G * M / K.c ^ 3
def horizonArea (M : ℝ) := 4 * Real.pi * (radius K M) ^ 2
def planckArea := K.hbar * K.G / K.c ^ 3
def entropy (M : ℝ) := K.kB * horizonArea K M / (4 * planckArea K)
def temperature (M : ℝ) := K.hbar * K.c ^ 3 / (8 * Real.pi * K.G * M * K.kB)
def energy (M : ℝ) := M * K.c ^ 2

theorem radius_time (M : ℝ) : radius K M = 2 * K.c * gravitationalTime K M := by
  unfold radius gravitationalTime
  field_simp [ne_of_gt K.c_pos]
  ring

theorem area_mass (M : ℝ) : horizonArea K M = 16 * Real.pi * K.G ^ 2 * M ^ 2 / K.c ^ 4 := by
  unfold horizonArea radius
  ring

theorem entropy_mass (M : ℝ) : entropy K M = 4 * Real.pi * K.kB * K.G * M ^ 2 / (K.hbar * K.c) := by
  unfold entropy planckArea
  rw [area_mass]
  field_simp [ne_of_gt K.G_pos, ne_of_gt K.hbar_pos, ne_of_gt K.c_pos]
  ring

theorem temperature_time (M : ℝ) : temperature K M = K.hbar / (8 * Real.pi * K.kB * gravitationalTime K M) := by
  unfold temperature gravitationalTime
  field_simp [ne_of_gt K.c_pos]
  ring

/-- Main claim eq:smarr, derived from area-based entropy and Hawking temperature. -/
theorem smarr (M : ℝ) (hM : 0 < M) : 2 * temperature K M * entropy K M = energy K M := by
  have hG := ne_of_gt K.G_pos
  have hc := ne_of_gt K.c_pos
  have hh := ne_of_gt K.hbar_pos
  have hk := ne_of_gt K.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have hm := ne_of_gt hM
  rw [entropy_mass]
  unfold temperature energy
  field_simp
  ring

theorem thermal_time (M : ℝ) (_hM : 0 < M) :
    K.hbar / (K.kB * temperature K M) = 8 * Real.pi * gravitationalTime K M := by
  unfold temperature gravitationalTime
  field_simp [ne_of_gt Real.pi_pos, ne_of_gt K.G_pos, ne_of_gt K.hbar_pos,
    ne_of_gt K.c_pos, ne_of_gt K.kB_pos]
  ring

/-- h is explicitly 2*pi*hbar; this is energy in frequency units, not a spectral peak. -/
theorem thermal_frequency (M : ℝ) (hM : 0 < M) :
    K.kB * temperature K M / (2 * Real.pi * K.hbar) =
      1 / (16 * Real.pi ^ 2 * gravitationalTime K M) := by
  have hG := ne_of_gt K.G_pos
  have hc := ne_of_gt K.c_pos
  have hh := ne_of_gt K.hbar_pos
  have hk := ne_of_gt K.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have hm := ne_of_gt hM
  unfold temperature gravitationalTime
  field_simp
  ring

theorem entropy_difference (Ma Mb : ℝ) : entropy K Mb - entropy K Ma =
    (4 * Real.pi * K.kB * K.G / (K.hbar * K.c)) * (Mb ^ 2 - Ma ^ 2) := by
  rw [entropy_mass, entropy_mass]
  ring

theorem entropy_hasDerivAt (M : ℝ) : HasDerivAt (entropy K)
    ((4 * Real.pi * K.kB * K.G / (K.hbar * K.c)) * (2 * M)) M := by
  have hf : entropy K = fun m => (4 * Real.pi * K.kB * K.G / (K.hbar * K.c)) * m ^ 2 := by
    funext m
    rw [entropy_mass]
    ring
  rw [hf]
  simpa using ((hasDerivAt_id M).pow 2).const_mul (4 * Real.pi * K.kB * K.G / (K.hbar * K.c))

theorem energy_hasDerivAt (M : ℝ) : HasDerivAt (energy K) (K.c ^ 2) M := by
  simpa [energy] using (hasDerivAt_id M).mul_const (K.c ^ 2)

/-- Differential first-law consistency along the mass-parametrized family. -/
theorem first_law_mass (M : ℝ) (hM : 0 < M) :
    temperature K M * deriv (entropy K) M = K.c ^ 2 := by
  have hG := ne_of_gt K.G_pos
  have hc := ne_of_gt K.c_pos
  have hh := ne_of_gt K.hbar_pos
  have hk := ne_of_gt K.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have hm := ne_of_gt hM
  rw [(entropy_hasDerivAt K M).deriv]
  unfold temperature
  field_simp
  ring

theorem first_law (M : ℝ) (hM : 0 < M) :
    deriv (energy K) M = temperature K M * deriv (entropy K) M := by
  rw [(energy_hasDerivAt K M).deriv, first_law_mass K M hM]

/-- Rewrite S(M) as C E^2 with E=Mc^2. -/
theorem entropy_energy (M : ℝ) : entropy K M =
    (4 * Real.pi * K.kB * K.G / (K.hbar * K.c ^ 5)) * energy K M ^ 2 := by
  rw [entropy_mass]
  unfold energy
  field_simp [ne_of_gt K.c_pos, ne_of_gt K.hbar_pos]
  ring

theorem quadratic_entropy_hasDerivAt (C E : ℝ) :
    HasDerivAt (fun x : ℝ => C * x ^ 2) (2 * C * E) E := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using ((hasDerivAt_id E).pow 2).const_mul C

theorem quadratic_entropy_slope (C E : ℝ) (hE : E ≠ 0) :
    deriv (fun x : ℝ => C * x ^ 2) E = 2 * (C * E ^ 2) / E := by
  rw [(quadratic_entropy_hasDerivAt C E).deriv]
  field_simp
  ring

/-- Factor two from quadratic entropy and the differential first law. -/
theorem smarr_from_first_law (C E T : ℝ)
    (hfirst : T * deriv (fun x : ℝ => C * x ^ 2) E = 1) :
    E = 2 * T * (C * E ^ 2) := by
  rw [(quadratic_entropy_hasDerivAt C E).deriv] at hfirst
  calc
    E = (T * (2 * C * E)) * E := by rw [hfirst]; ring
    _ = 2 * T * (C * E ^ 2) := by ring

/-- An entropy offset does not change its derivative. -/
theorem offset_entropy_hasDerivAt (C E S₀ : ℝ) :
    HasDerivAt (fun x : ℝ => C * x ^ 2 + S₀) (2 * C * E) E := by
  simpa using (quadratic_entropy_hasDerivAt C E).add (hasDerivAt_const E S₀)

/-- Shows why an unspecified additive entropy constant cannot be ignored. -/
theorem offset_smarr (C E T S₀ : ℝ)
    (hfirst : T * deriv (fun x : ℝ => C * x ^ 2 + S₀) E = 1) :
    2 * T * (C * E ^ 2 + S₀) = E + 2 * T * S₀ := by
  rw [(offset_entropy_hasDerivAt C E S₀).deriv] at hfirst
  calc
    2 * T * (C * E ^ 2 + S₀) = (T * (2 * C * E)) * E + 2 * T * S₀ := by ring
    _ = E + 2 * T * S₀ := by rw [hfirst]; ring

#print axioms radius_time
#print axioms area_mass
#print axioms entropy_mass
#print axioms temperature_time
#print axioms smarr
#print axioms thermal_time
#print axioms thermal_frequency
#print axioms entropy_difference
#print axioms entropy_hasDerivAt
#print axioms energy_hasDerivAt
#print axioms first_law_mass
#print axioms first_law
#print axioms entropy_energy
#print axioms quadratic_entropy_hasDerivAt
#print axioms quadratic_entropy_slope
#print axioms smarr_from_first_law
#print axioms offset_entropy_hasDerivAt
#print axioms offset_smarr

end
end SmarrPilot
