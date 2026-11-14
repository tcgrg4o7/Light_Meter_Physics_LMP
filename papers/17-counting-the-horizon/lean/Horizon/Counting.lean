import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Manuscript 17, source commit a0854589764f512c886f1d9e7328956f321df836.
Schwarzschild radius, spherical area, Planck area, area entropy and Hawking
temperature are model inputs. No microscopic degrees of freedom are postulated.
All count-like quantities are real ratios, not natural-number counts of tiles.
-/
namespace Horizon

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
def area (M : ℝ) := 4 * Real.pi * (radius K M) ^ 2
def planckArea := K.hbar * K.G / K.c ^ 3
def areaRatio (M : ℝ) := area K M / planckArea K
def entropy (M : ℝ) := K.kB * area K M / (4 * planckArea K)
def entropyNats (M : ℝ) := entropy K M / K.kB
def entropyBits (M : ℝ) := entropy K M / (K.kB * Real.log 2)
def temperature (M : ℝ) := K.hbar * K.c ^ 3 / (8 * Real.pi * K.G * M * K.kB)
def energy (M : ℝ) := M * K.c ^ 2
def planckConstant := 2 * Real.pi * K.hbar
def massFrequency (M : ℝ) := energy K M / planckConstant K
def thermalFrequency (M : ℝ) := K.kB * temperature K M / planckConstant K

theorem log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)

theorem area_mass (M : ℝ) : area K M = 16 * Real.pi * K.G ^ 2 * M ^ 2 / K.c ^ 4 := by
  unfold area radius
  ring

theorem area_ratio_mass (M : ℝ) : areaRatio K M = 16 * Real.pi * K.G * M ^ 2 / (K.hbar * K.c) := by
  have hG := ne_of_gt K.G_pos
  have hc := ne_of_gt K.c_pos
  have hh := ne_of_gt K.hbar_pos
  unfold areaRatio planckArea
  rw [area_mass]
  field_simp
  ring

theorem entropy_nats (M : ℝ) : entropyNats K M = areaRatio K M / 4 := by
  have hk := ne_of_gt K.kB_pos
  have hP : planckArea K ≠ 0 := ne_of_gt (div_pos (mul_pos K.hbar_pos K.G_pos) (pow_pos K.c_pos 3))
  have hl := ne_of_gt log_two_pos
  unfold entropyNats entropy areaRatio
  field_simp
  ring

theorem entropy_bits (M : ℝ) : entropyBits K M = areaRatio K M / (4 * Real.log 2) := by
  have hk := ne_of_gt K.kB_pos
  have hP : planckArea K ≠ 0 := ne_of_gt (div_pos (mul_pos K.hbar_pos K.G_pos) (pow_pos K.c_pos 3))
  have hl := ne_of_gt log_two_pos
  unfold entropyBits entropy areaRatio
  field_simp
  ring

theorem nats_from_bits (M : ℝ) : entropyNats K M = Real.log 2 * entropyBits K M := by
  have hl := ne_of_gt log_two_pos
  rw [entropy_nats, entropy_bits]
  field_simp
  ring

theorem area_from_bits (M : ℝ) : areaRatio K M = (4 * Real.log 2) * entropyBits K M := by
  have hl := ne_of_gt log_two_pos
  rw [entropy_bits]
  field_simp

theorem area_ratio_pos (M : ℝ) (hM : 0 < M) : 0 < areaRatio K M := by
  rw [area_ratio_mass]
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) K.G_pos) (sq_pos_of_pos hM))
    (mul_pos K.hbar_pos K.c_pos)

theorem entropy_bits_pos (M : ℝ) (hM : 0 < M) : 0 < entropyBits K M := by
  rw [entropy_bits]
  exact div_pos (area_ratio_pos K M hM) (mul_pos (by norm_num) log_two_pos)

theorem temperature_pos (M : ℝ) (hM : 0 < M) : 0 < temperature K M := by
  unfold temperature
  exact div_pos (mul_pos K.hbar_pos (pow_pos K.c_pos 3))
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) K.G_pos) hM) K.kB_pos)

/-- Equipartition-shaped algebra; no physical mode count is assumed or proved. -/
theorem area_energy_identity (M : ℝ) (hM : 0 < M) :
    energy K M = (areaRatio K M / 2) * K.kB * temperature K M := by
  have hG := ne_of_gt K.G_pos
  have hc := ne_of_gt K.c_pos
  have hh := ne_of_gt K.hbar_pos
  have hk := ne_of_gt K.kB_pos
  have hp := ne_of_gt Real.pi_pos
  have hm := ne_of_gt hM
  rw [area_ratio_mass]
  unfold energy temperature
  field_simp
  ring

theorem smarr (M : ℝ) (hM : 0 < M) : energy K M = 2 * temperature K M * entropy K M := by
  have hs : entropy K M = K.kB * areaRatio K M / 4 := by
    unfold entropy areaRatio
    ring
  rw [area_energy_identity K M hM, hs]
  ring

theorem bit_energy_identity (M : ℝ) (hM : 0 < M) :
    energy K M = 2 * Real.log 2 * entropyBits K M * K.kB * temperature K M := by
  rw [area_energy_identity K M hM, area_from_bits]
  ring

theorem area_frequency_identity (M : ℝ) (hM : 0 < M) :
    massFrequency K M = (areaRatio K M / 2) * thermalFrequency K M := by
  unfold massFrequency thermalFrequency
  rw [area_energy_identity K M hM]
  ring

theorem bit_frequency_identity (M : ℝ) (hM : 0 < M) :
    massFrequency K M = 2 * Real.log 2 * entropyBits K M * thermalFrequency K M := by
  unfold massFrequency thermalFrequency
  rw [bit_energy_identity K M hM]
  ring

theorem angular_frequency (M : ℝ) :
    energy K M / K.hbar = 2 * Real.pi * massFrequency K M := by
  have hp := ne_of_gt Real.pi_pos
  have hh := ne_of_gt K.hbar_pos
  unfold massFrequency planckConstant
  field_simp
  ring

theorem area_ratio_scaling (M a : ℝ) : areaRatio K (a * M) = a ^ 2 * areaRatio K M := by
  rw [area_ratio_mass, area_ratio_mass]
  ring

theorem bits_scaling (M a : ℝ) : entropyBits K (a * M) = a ^ 2 * entropyBits K M := by
  rw [entropy_bits, entropy_bits, area_ratio_scaling]
  ring

theorem temperature_scaling (M a : ℝ) (_ha : 0 < a) :
    temperature K (a * M) = temperature K M / a := by
  unfold temperature
  ring

theorem mass_frequency_scaling (M a : ℝ) : massFrequency K (a * M) = a * massFrequency K M := by
  unfold massFrequency energy
  ring

theorem thermal_frequency_scaling (M a : ℝ) (ha : 0 < a) :
    thermalFrequency K (a * M) = thermalFrequency K M / a := by
  unfold thermalFrequency
  rw [temperature_scaling K M a ha]
  ring

/-- The half-area coefficient becomes 2 ln 2 per entropy-bit unit. -/
theorem coefficient_conversion (M : ℝ) :
    areaRatio K M / 2 = 2 * Real.log 2 * entropyBits K M := by
  rw [area_from_bits]
  ring

#print axioms log_two_pos
#print axioms area_mass
#print axioms area_ratio_mass
#print axioms entropy_nats
#print axioms entropy_bits
#print axioms nats_from_bits
#print axioms area_from_bits
#print axioms area_ratio_pos
#print axioms entropy_bits_pos
#print axioms temperature_pos
#print axioms area_energy_identity
#print axioms smarr
#print axioms bit_energy_identity
#print axioms area_frequency_identity
#print axioms bit_frequency_identity
#print axioms angular_frequency
#print axioms area_ratio_scaling
#print axioms bits_scaling
#print axioms temperature_scaling
#print axioms mass_frequency_scaling
#print axioms thermal_frequency_scaling
#print axioms coefficient_conversion

end
end Horizon
