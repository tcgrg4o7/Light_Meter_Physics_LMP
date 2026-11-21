import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace RadiusPowers

open Filter
open scoped Topology

noncomputable section

def compactness (g t : ℝ) : ℝ := g / t
def inverseTime (g t : ℝ) : ℝ := g / t ^ 2
def tidalScale (g t : ℝ) : ℝ := g / t ^ 3

/-- Derivative with respect to the radius light-time, holding gravitational time fixed. -/
theorem compactness_derivative (g t : ℝ) (ht : 0 < t) :
    HasDerivAt (compactness g) (-inverseTime g t) t := by
  have h := (hasDerivAt_id t).inv (ne_of_gt ht)
  convert HasDerivAt.const_mul g h using 1
  dsimp [inverseTime]
  ring

theorem inverse_time_derivative (g t : ℝ) (ht : 0 < t) :
    HasDerivAt (inverseTime g) (-2 * tidalScale g t) t := by
  have hn : t ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
  have h := ((hasDerivAt_id t).pow 2).inv hn
  convert HasDerivAt.const_mul g h using 1
  dsimp [tidalScale]
  field_simp [ne_of_gt ht]
  ring

theorem ladder (g t : ℝ) (ht : 0 < t) :
    -deriv (compactness g) t = inverseTime g t ∧
    -(1 / 2 : ℝ) * deriv (inverseTime g) t = tidalScale g t := by
  rw [(compactness_derivative g t ht).deriv, (inverse_time_derivative g t ht).deriv]
  constructor <;> ring

/-- Independent circular balance: the supplied inward field is μ/r². -/
theorem circular_balance (μ r Ω : ℝ) (hr : 0 < r)
    (balance : r * Ω ^ 2 = μ / r ^ 2) : Ω ^ 2 = μ / r ^ 3 := by
  calc
    Ω ^ 2 = (r * Ω ^ 2) / r := by field_simp [ne_of_gt hr]
    _ = μ / r ^ 3 := by rw [balance]; ring

theorem light_time_conversion (μ r c : ℝ) (hc : 0 < c) (hr : 0 < r) :
    tidalScale (μ / c ^ 3) (r / c) = μ / r ^ 3 := by
  unfold tidalScale
  field_simp [ne_of_gt hc, ne_of_gt hr]

theorem second_derivative (g t : ℝ) (ht : 0 < t) :
    (1 / 2 : ℝ) * deriv (deriv (compactness g)) t = tidalScale g t := by
  have hEq : deriv (compactness g) =ᶠ[nhds t] fun x => -inverseTime g x :=
    (lt_mem_nhds ht).mono fun x hx => (compactness_derivative g x hx).deriv
  have h := HasDerivAt.congr_of_eventuallyEq (HasDerivAt.neg (inverse_time_derivative g t ht)) hEq
  rw [h.deriv]
  ring

theorem circular_rate_is_half_second_derivative (μ r c Ω : ℝ)
    (hc : 0 < c) (hr : 0 < r) (balance : r * Ω ^ 2 = μ / r ^ 2) :
    Ω ^ 2 = (1 / 2 : ℝ) * deriv (deriv (compactness (μ / c ^ 3))) (r / c) := by
  rw [second_derivative _ _ (div_pos hr hc), light_time_conversion μ r c hc hr]
  exact circular_balance μ r Ω hr balance

theorem doubling (g t : ℝ) (_ht : 0 < t) :
    compactness g (2*t) = compactness g t / 2 ∧
    inverseTime g (2*t) = inverseTime g t / 4 ∧
    tidalScale g (2*t) = tidalScale g t / 8 := by
  unfold compactness inverseTime tidalScale
  exact ⟨by ring, by ring, by ring⟩

end

#print axioms compactness_derivative
#print axioms inverse_time_derivative
#print axioms ladder
#print axioms circular_balance
#print axioms light_time_conversion
#print axioms second_derivative
#print axioms circular_rate_is_half_second_derivative
#print axioms doubling

end RadiusPowers
