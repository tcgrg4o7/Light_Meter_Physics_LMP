import ComptonPilot.Exact
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ComptonPilot

noncomputable def lorentzGamma (c v : ℝ) : ℝ :=
  1 / Real.sqrt (1 - v ^ 2 / c ^ 2)

theorem subluminal_gap (c v : ℝ) (_hc : 0 < c) (hv : |v| < c) :
    0 < c ^ 2 - v ^ 2 := by
  have hb := abs_lt.mp hv
  have hprod := mul_pos (sub_pos.mpr hb.2) (show 0 < c + v by linarith)
  nlinarith

theorem gamma_radicand_pos (c v : ℝ) (hc : 0 < c) (hv : |v| < c) :
    0 < 1 - v ^ 2 / c ^ 2 := by
  have hsq : 0 < c ^ 2 := sq_pos_of_pos hc
  have hlt : v ^ 2 / c ^ 2 < 1 :=
    (div_lt_one hsq).2 (by linarith [subluminal_gap c v hc hv])
  linarith

theorem lorentzGamma_pos (c v : ℝ) (hc : 0 < c) (hv : |v| < c) :
    0 < lorentzGamma c v := by
  exact div_pos zero_lt_one (Real.sqrt_pos.2 (gamma_radicand_pos c v hc hv))

/-- Gamma normalization is now derived, not postulated. -/
theorem lorentzGamma_normalization (c v : ℝ) (hc : 0 < c) (hv : |v| < c) :
    lorentzGamma c v ^ 2 * (c ^ 2 - v ^ 2) = c ^ 2 := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hs := Real.sq_sqrt (le_of_lt (gamma_radicand_pos c v hc hv))
  have hs0 : Real.sqrt (1 - v ^ 2 / c ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (gamma_radicand_pos c v hc hv))
  have hgap : c ^ 2 - v ^ 2 = Real.sqrt (1 - v ^ 2 / c ^ 2) ^ 2 * c ^ 2 := by
    rw [hs]
    field_simp [hc0]
  unfold lorentzGamma
  rw [hgap]
  rw [div_pow, one_pow, one_div, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 2 hs0), one_mul]

/-- Physical specialization of the algebraic path-frequency theorem. -/
theorem pathFrequency_from_subluminal
    (E p m c v h : ℝ) (hc : 0 < c) (hv : |v| < c)
    (hE : E = lorentzGamma c v * m * c ^ 2)
    (hp : p = lorentzGamma c v * m * v) :
    (E - p * v) / h = comptonFrequency m c h / lorentzGamma c v := by
  exact pathFrequency_eq_compton_div_gamma E p (lorentzGamma c v) m c v h
    (ne_of_gt (lorentzGamma_pos c v hc hv)) hE hp
    (lorentzGamma_normalization c v hc hv)

theorem energy_minus_momentum_velocity_pos
    (E p m c v : ℝ) (hm : 0 < m) (hc : 0 < c) (hv : |v| < c)
    (hE : E = lorentzGamma c v * m * c ^ 2)
    (hp : p = lorentzGamma c v * m * v) : 0 < E - p * v := by
  have hid : E - p * v = (m * c ^ 2) / lorentzGamma c v := by
    simpa [comptonFrequency] using pathFrequency_from_subluminal E p m c v 1 hc hv hE hp
  rw [hid]
  exact div_pos (mul_pos hm (sq_pos_of_pos hc)) (lorentzGamma_pos c v hc hv)

/-- Signed derivative of phase in cycles along the inertial path x₀+vt. -/
theorem phaseCycles_hasDerivAt (E p h x₀ v t : ℝ) :
    HasDerivAt (fun s : ℝ => (p * (x₀ + v * s) - E * s) / h)
      ((p * v - E) / h) t := by
  simpa using ((((hasDerivAt_const t x₀).add ((hasDerivAt_id t).const_mul v)).const_mul p).sub
    ((hasDerivAt_id t).const_mul E)).div_const h

/-- Absolute cycles-per-time rate: the 1D eq:path-phase-rate bridge. -/
theorem abs_phaseCycles_deriv
    (E p m c v h x₀ t : ℝ) (hm : 0 < m) (hc : 0 < c) (hh : 0 < h)
    (hv : |v| < c) (hE : E = lorentzGamma c v * m * c ^ 2)
    (hp : p = lorentzGamma c v * m * v) :
    |deriv (fun s : ℝ => (p * (x₀ + v * s) - E * s) / h) t| =
      comptonFrequency m c h / lorentzGamma c v := by
  rw [(phaseCycles_hasDerivAt E p h x₀ v t).deriv]
  rw [show (p * v - E) / h = -((E - p * v) / h) by ring, abs_neg]
  rw [abs_of_pos (div_pos (energy_minus_momentum_velocity_pos E p m c v hm hc hv hE hp) hh)]
  exact pathFrequency_from_subluminal E p m c v h hc hv hE hp

#print axioms subluminal_gap
#print axioms gamma_radicand_pos
#print axioms lorentzGamma_pos
#print axioms lorentzGamma_normalization
#print axioms pathFrequency_from_subluminal
#print axioms energy_minus_momentum_velocity_pos
#print axioms phaseCycles_hasDerivAt
#print axioms abs_phaseCycles_deriv

end ComptonPilot
