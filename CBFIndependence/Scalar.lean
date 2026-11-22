import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace CBFIndependence
open Set Metric Filter Topology

/-- The squared normal displacement decreases along every solution on a
convex time interval. No uniqueness or differentiability of α is needed. -/
theorem normal_sq_antitone {D : Set ℝ} (conv : Convex ℝ D) {r α : ℝ → ℝ}
    (ode : ∀ t ∈ D, HasDerivWithinAt r (-α (r t)) D t)
    (sign : ∀ t ∈ D, 0 ≤ r t * α (r t)) :
    AntitoneOn (fun t => r t * r t) D := by
  have hd := fun t (ht : t ∈ D) => (ode t ht).mul (ode t ht)
  apply antitoneOn_of_hasDerivWithinAt_nonpos conv
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
  intro t ht
  nlinarith [sign t (interior_subset ht)]

/-- On a global, trapped forward solution, the continuous strictly restoring
normal term drives the normal coordinate to zero. -/
theorem normal_tendsto_zero {r α : ℝ → ℝ} {R : ℝ}
    (ha : ContinuousOn α (Icc (-R) R))
    (trapped : ∀ t ∈ Ici (0 : ℝ), r t ∈ Icc (-R) R)
    (ode : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt r (-α (r t)) (Ici 0) t)
    (sign : ∀ x ∈ Icc (-R) R, x ≠ 0 → 0 < x * α x) :
    Tendsto r atTop (𝓝 0) := by
  have hanti := normal_sq_antitone (convex_Ici (0 : ℝ)) ode (by
    intro t ht
    by_cases h : r t = 0
    · simp [h]
    · exact (sign _ (trapped t ht) h).le)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have enters : ∃ t ∈ Ici (0 : ℝ), |r t| < ε := by
    by_contra! avoid
    let A := Icc (-R) R ∩ {x : ℝ | ε ≤ |x|}
    have compactA : IsCompact A := isCompact_Icc.inter_right
      (isClosed_le continuous_const continuous_abs)
    have inA : ∀ t ∈ Ici (0 : ℝ), r t ∈ A := fun t ht => ⟨trapped t ht, avoid t ht⟩
    obtain ⟨s, hs, hmin⟩ := compactA.exists_isMinOn ⟨r 0, inA 0 (by simp)⟩
      (continuousOn_id.mul (ha.mono (show A ⊆ Icc (-R) R from inter_subset_left)))
    have hs0 : s ≠ 0 := by
      have he := hs.2
      intro heq
      simp [heq] at he
      linarith
    let m := s * α s
    have hm : 0 < m := sign s hs.1 hs0
    have bound : ∀ t ∈ Ici (0 : ℝ), m ≤ r t * α (r t) :=
      fun t ht => isMinOn_iff.mp hmin _ (inA t ht)
    have hd := fun t (ht : t ∈ Ici (0 : ℝ)) =>
      ((ode t ht).mul (ode t ht)).add
        (((hasDerivAt_id t).const_mul m).hasDerivWithinAt (s := Ici 0))
    have descent : AntitoneOn (fun t => r t * r t + m * t) (Ici 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
        (fun t ht => (hd t ht).continuousWithinAt)
        (fun t ht => (hd t (interior_subset ht)).mono interior_subset)
      intro t ht
      nlinarith [bound t (interior_subset ht)]
    let t := r 0 ^ 2 / m + 1
    have ht : 0 ≤ t := by dsimp [t]; positivity
    have hcontra := descent (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
    have hid : m * t = r 0 ^ 2 + m := by dsimp [t]; field_simp
    change r t * r t + m * t ≤ r 0 * r 0 + m * 0 at hcontra
    rw [hid] at hcontra
    nlinarith [sq_nonneg (r t)]
  obtain ⟨s, hs, hεs⟩ := enters
  filter_upwards [eventually_ge_atTop s] with t ht
  have h := hanti hs (le_trans hs ht) ht
  rw [Real.dist_eq, sub_zero]
  have hsquares : (r t)^2 ≤ (r s)^2 := by simpa [pow_two] using h
  exact (sq_le_sq.mp hsquares).trans_lt hεs

end CBFIndependence
