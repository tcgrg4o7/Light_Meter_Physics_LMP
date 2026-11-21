import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace SchwarzschildTides

noncomputable section

def tidalScale (tg tr : ℝ) : ℝ := tg / tr ^ 3

/-- Substitutes the six supplied orthonormal pair components; each occurs
    four times in the ordered contraction, with positive metric-sign product. -/
def contraction (k : ℝ) : ℝ :=
  4 * ((-2*k)^2 + k^2 + k^2 + (2*k)^2 + (-k)^2 + (-k)^2)

def kretschmann (c q : ℝ) : ℝ := contraction (q / c ^ 2)

theorem trace_free (q : ℝ) : 2*q + (-q) + (-q) = 0 := by ring

theorem contraction_eq (k : ℝ) : contraction k = 48*k^2 := by
  unfold contraction
  ring

theorem invariant_scale (c q : ℝ) : kretschmann c q = 48 / c ^ 4 * q ^ 2 := by
  unfold kretschmann
  rw [contraction_eq]
  ring

theorem scale_from_invariant (c q : ℝ) (hc : 0 < c) (hq : 0 ≤ q) :
    c ^ 2 * Real.sqrt (kretschmann c q / 48) = q := by
  unfold kretschmann
  rw [contraction_eq, show 48 * (q / c ^ 2)^2 / 48 = (q / c ^ 2)^2 by ring,
    Real.sqrt_sq (div_nonneg hq (by positivity))]
  field_simp [ne_of_gt hc]

theorem horizon_scale (tg : ℝ) (hg : 0 < tg) :
    tidalScale tg (2*tg) = 1 / (8*tg^2) := by
  unfold tidalScale
  field_simp [ne_of_gt hg]
  ring

theorem horizon_acceleration_coefficients (tg : ℝ) (hg : 0 < tg) :
    2 * tidalScale tg (2*tg) = 1 / (4*tg^2) ∧
    -tidalScale tg (2*tg) = -(1 / (8*tg^2)) := by
  rw [horizon_scale tg hg]
  exact ⟨by ring, rfl⟩

theorem horizon_curvature (c tg : ℝ) (hc : 0 < c) (hg : 0 < tg) :
    kretschmann c (tidalScale tg (2*tg)) = 12 / (2*c*tg)^4 := by
  rw [horizon_scale tg hg, invariant_scale]
  field_simp [ne_of_gt hc, ne_of_gt hg]
  ring

theorem horizon_mass_scaling (c tg s : ℝ) (hc : 0 < c) (hg : 0 < tg)
    (hs : 0 < s) :
    tidalScale (s*tg) (2*(s*tg)) = tidalScale tg (2*tg) / s^2 ∧
    kretschmann c (tidalScale (s*tg) (2*(s*tg))) =
      kretschmann c (tidalScale tg (2*tg)) / s^4 := by
  have hsg : 0 < s * tg := mul_pos hs hg
  constructor
  · rw [horizon_scale (s*tg) hsg, horizon_scale tg hg]
    ring
  · rw [horizon_curvature c (s*tg) hc hsg, horizon_curvature c tg hc hg]
    ring

/-- With initially stationary semiaxes, the first product derivative is zero. -/
theorem initial_volume_rate (R A B : ℝ → ℝ) (t : ℝ)
    (hR : HasDerivAt R 0 t) (hA : HasDerivAt A 0 t) (hB : HasDerivAt B 0 t) :
    HasDerivAt (fun u => R u * A u * B u) 0 t := by
  simpa using (hR.mul hA).mul hB

/-- The product-rule acceleration at release, for the specified three tides
    and zero relative velocities; this is not a finite-time volume law. -/
theorem initial_volume_acceleration (R A B dR dA dB : ℝ → ℝ) (t q : ℝ)
    (hR : ∀ u, HasDerivAt R (dR u) u)
    (hA : ∀ u, HasDerivAt A (dA u) u)
    (hB : ∀ u, HasDerivAt B (dB u) u)
    (zR : dR t = 0) (zA : dA t = 0) (zB : dB t = 0)
    (ddR : HasDerivAt dR (2*q*R t) t)
    (ddA : HasDerivAt dA (-q*A t) t) (ddB : HasDerivAt dB (-q*B t) t) :
    HasDerivAt (deriv (fun u => R u * A u * B u)) 0 t := by
  have dV : deriv (fun u => R u * A u * B u) =
      fun u => dR u * A u * B u + R u * dA u * B u + R u * A u * dB u := by
    funext u
    rw [(((hR u).mul (hA u)).mul (hB u)).deriv]
    ring
  rw [dV]
  apply HasDerivAt.congr_deriv
    (HasDerivAt.add
      (HasDerivAt.add ((ddR.mul (hA t)).mul (hB t)) (((hR t).mul ddA).mul (hB t)))
      (((hR t).mul (hA t)).mul ddB))
  simp [zR, zA, zB]
  ring

/-- This compares two distinct trace-free spectra, not spacetime invariants. -/
theorem plane_wave_contrast (q w : ℝ) (hq : 0 < q) :
    w + (-w) + 0 = 0 ∧ (2*q, -q, -q) ≠ (w, -w, 0) := by
  refine ⟨by ring, ?_⟩
  intro h
  have hh := congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) h
  dsimp at hh
  linarith only [hh, hq]

end

#print axioms trace_free
#print axioms contraction_eq
#print axioms invariant_scale
#print axioms scale_from_invariant
#print axioms horizon_scale
#print axioms horizon_acceleration_coefficients
#print axioms horizon_curvature
#print axioms horizon_mass_scaling
#print axioms initial_volume_rate
#print axioms initial_volume_acceleration
#print axioms plane_wave_contrast

end SchwarzschildTides
