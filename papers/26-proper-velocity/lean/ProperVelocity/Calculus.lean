import ProperVelocity.Algebra
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ProperVelocity
noncomputable section

theorem proper_chain_rule {x t : ℝ → ℝ} {tau c v : ℝ}
    (hx : HasDerivAt x v (t tau)) (ht : HasDerivAt t (gamma c v) tau) :
    HasDerivAt (fun s => x (t s)) (proper c v) tau := by
  simpa [proper, mul_comm] using hx.comp tau ht

theorem fixed_mass_force {u : ℝ → ℝ} {a t m : ℝ} (hu : HasDerivAt u a t) :
    HasDerivAt (fun s => m * u s) (m * a) t := hu.const_mul m

theorem proper_derivative {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    HasDerivAt (proper c) (gamma c v ^ 3) v := by
  have hn := ne_of_gt hc
  have hr := radicand_pos hc hv
  have hs := ne_of_gt (Real.sqrt_pos.2 hr)
  have he := Real.sq_sqrt (le_of_lt hr)
  have hd := (((hasDerivAt_id v).div_const c).pow 2).const_sub 1
  have hroot := hd.sqrt (ne_of_gt hr)
  have hdiv := (hasDerivAt_id v).div hroot hs
  have hf : (fun x => x / Real.sqrt (1 - (x / c) ^ 2)) = proper c := by
    funext x
    unfold proper gamma
    ring
  simp only [id_eq] at hdiv
  rw [hf] at hdiv
  convert hdiv using 1
  unfold gamma
  generalize Real.sqrt (1 - (v / c) ^ 2) = s at *
  field_simp
  field_simp at he
  nlinarith [congrArg (fun z : ℝ => z * (2 * s ^ 3)) he]

theorem longitudinal_acceleration {v : ℝ → ℝ} {c a t : ℝ}
    (hc : 0 < c) (hv : |v t| < c) (ha : HasDerivAt v a t) :
    HasDerivAt (fun s => proper c (v s)) (gamma c (v t) ^ 3 * a) t :=
  (proper_derivative hc hv).comp t ha

theorem longitudinal_force {v : ℝ → ℝ} {c a t m : ℝ}
    (hc : 0 < c) (hv : |v t| < c) (ha : HasDerivAt v a t) :
    HasDerivAt (fun s => momentum m c (v s)) (m * gamma c (v t) ^ 3 * a) t := by
  have h := (longitudinal_acceleration hc hv ha).const_mul m
  simpa only [momentum_eq_mass_proper, mul_assoc] using h

#print axioms proper_chain_rule
#print axioms fixed_mass_force
#print axioms proper_derivative
#print axioms longitudinal_acceleration
#print axioms longitudinal_force
end
end ProperVelocity
