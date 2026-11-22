import CBFIndependence.Statement
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Local activity of one barrier constraint in convex optimization. -/

namespace CBFIndependence

open Set Filter Topology

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A strictly slack continuous inequality can be dropped locally. Convexity
then turns this local minimum into a global minimum of the original problem. -/
theorem solves_base_of_slack {K : Set W} {L c : W → ℝ} {v : W}
    (hv : Solves L (filtered K c) v) (hc : ContinuousAt c v)
    (hL : ConvexOn ℝ K L) (slack : 0 < c v) : Solves L K v := by
  refine ⟨hv.1.1, IsMinOn.of_isLocalMinOn_of_convexOn hv.1.1 ?_ hL⟩
  have hp : ∀ᶠ w in 𝓝 v, 0 < c w := hc.eventually (Ioi_mem_nhds slack)
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hk
  exact isMinOn_iff.mp hv.2 w ⟨hk, hw.le⟩

theorem residual_eq_zero_of_different_minimizers {K : Set W} {L c : W → ℝ} {v w : W}
    (hv : Solves L (filtered K c) v) (hw : Solves L K w)
    (hc : ContinuousAt c v) (hL : StrictConvexOn ℝ K L) (hne : v ≠ w) : c v = 0 := by
  apply le_antisymm _ hv.1.2
  by_contra! hpos
  have h := solves_base_of_slack hv hc hL.convexOn hpos
  exact hne (hL.eq_of_isMinOn h.2 hw.2 h.1 hw.1)

variable {X : Type*} [TopologicalSpace X]

/-- The two decision maps need only be continuous at the equilibrium.
Strict inequality of their values persists, forcing activity on a neighborhood.
The optimization continuity theorem supplies the two continuity premises. -/
theorem eventually_active {p : X} {K : X → Set W} {L c : X → W → ℝ} {v w : X → W}
    (hv : ∀ᶠ x in 𝓝 p, Solves (L x) (filtered (K x) (c x)) (v x))
    (hw : ∀ᶠ x in 𝓝 p, Solves (L x) (K x) (w x))
    (hL : ∀ᶠ x in 𝓝 p, StrictConvexOn ℝ (K x) (L x))
    (hc : ∀ᶠ x in 𝓝 p, ContinuousAt (c x) (v x))
    (cv : ContinuousAt v p) (cw : ContinuousAt w p) (hne : v p ≠ w p) :
    ∀ᶠ x in 𝓝 p, c x (v x) = 0 := by
  have hd := (cv.ne_iff_eventually_ne cw).mp hne
  filter_upwards [hv, hw, hL, hc, hd] with x h₁ h₀ hLx hcx hx
  exact residual_eq_zero_of_different_minimizers h₁ h₀ hcx hLx hx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The optimizer at an undesirable equilibrium lies on the zero level.
Strict feasibility at that point also rules out a zero normal covector. -/
theorem zero_level_and_regular_of_undesirable
    {K : Set W} {L : W → ℝ} {plant : W → E} {v w : W} {n : E →L[ℝ] ℝ}
    {r : ℝ} {α : ℝ → ℝ}
    (sign : r ≠ 0 → 0 < r * α r) (atZero : α 0 = 0)
    (hL : StrictConvexOn ℝ K L) (cont : Continuous plant)
    (hv : Solves L (filtered K (fun y => n (plant y) + α r)) v)
    (hw : Solves L K w) (eqm : plant v = 0) (nominal : plant w ≠ 0)
    (slater : ∃ s ∈ K, 0 < n (plant s) + α r) : r = 0 ∧ n ≠ 0 := by
  have hne : v ≠ w := fun e => nominal (e ▸ eqm)
  have ha := residual_eq_zero_of_different_minimizers hv hw
    ((n.continuous.comp cont).add continuous_const).continuousAt hL hne
  rw [eqm, map_zero, zero_add] at ha
  have hr : r = 0 := by
    by_contra h
    simpa [ha] using sign h
  refine ⟨hr, ?_⟩
  rintro rfl
  obtain ⟨s, _, hs⟩ := slater
  simp [hr, atZero] at hs

/-- Positive scaling of the normal gives the same feasible half-space. -/
theorem filtered_scale {D : Type*} {K : Set D} {c : D → ℝ} {a : ℝ} (ha : 0 < a) :
    filtered K (fun w => a * c w) = filtered K c := by
  ext w
  simp [filtered, ha]

end CBFIndependence
