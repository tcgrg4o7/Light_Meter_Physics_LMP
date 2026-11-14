import ProperVelocity.Calculus

namespace ProperVelocity
noncomputable section

theorem gamma_at_least_one {c v : ℝ} (hc : 0 < c) (hv : |v| < c) :
    1 ≤ gamma c v := by
  have h := proper_hyperbola hc hv
  have hp := gamma_pos hc hv
  nlinarith [sq_nonneg (proper c v / c)]

theorem coordinate_sign {c u : ℝ} : 0 < coordinate c u ↔ 0 < u := by
  unfold coordinate
  exact div_pos_iff_of_pos_right (inverse_sqrt_pos c u)

theorem coordinate_odd (c u : ℝ) : coordinate c (-u) = -coordinate c u := by
  unfold coordinate
  have h : (-u / c) ^ 2 = (u / c) ^ 2 := by ring
  rw [h]
  ring

theorem every_proper_velocity {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ∃ v : ℝ, |v| < c ∧ proper c v = u :=
  ⟨coordinate c u, coordinate_bound hc u, proper_of_coordinate hc u⟩

theorem positive_threshold {c : ℝ} (hc : 0 < c) :
    coordinate c c = c / Real.sqrt 2 := by
  unfold coordinate
  rw [div_self (ne_of_gt hc)]
  norm_num

theorem negative_threshold {c : ℝ} (hc : 0 < c) :
    coordinate c (-c) = -(c / Real.sqrt 2) := by
  rw [coordinate_odd, positive_threshold hc]

theorem example_gamma {c : ℝ} (hc : 0 < c) : gamma c ((4 / 5 : ℝ) * c) = 5 / 3 := by
  have hn := ne_of_gt hc
  have h : 1 - (((4 / 5 : ℝ) * c) / c) ^ 2 = (9 / 25 : ℝ) := by field_simp; ring
  have hs : Real.sqrt (9 / 25 : ℝ) = 3 / 5 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  unfold gamma
  rw [h, hs]
  norm_num

theorem example_proper {c : ℝ} (hc : 0 < c) :
    proper c ((4 / 5 : ℝ) * c) = (4 / 3 : ℝ) * c := by
  unfold proper
  rw [example_gamma hc]
  ring

/-- Exact arithmetic conditional on the rounded distance input, in light-years and years. -/
theorem example_journey :
    (106 / 25 : ℝ) / (4 / 5) = 53 / 10 ∧
    (53 / 10 : ℝ) / (5 / 3) = 159 / 50 ∧
    (106 / 25 : ℝ) / (159 / 50) = 4 / 3 ∧
    (106 / 25 : ℝ) / (5 / 3) = 318 / 125 ∧
    (318 / 125 : ℝ) / (4 / 5) = 159 / 50 := by norm_num

#print axioms gamma_at_least_one
#print axioms coordinate_sign
#print axioms coordinate_odd
#print axioms every_proper_velocity
#print axioms positive_threshold
#print axioms negative_threshold
#print axioms example_gamma
#print axioms example_proper
#print axioms example_journey
end
end ProperVelocity
