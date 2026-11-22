import CBFIndependence.Optimization
import CBFIndependence.Activation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace CBFIndependence
open Set Filter Topology Optimization
noncomputable section

variable {X W E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Program
variable {q : ℕ} (P : Program X W q)

theorem local_decision {p : X} (hs : P.slater p) :
    (∀ᶠ x in 𝓝 p, Solves (P.cost x) (P.domain x) (P.decision x)) ∧
    ContinuousAt P.decision p := by
  obtain ⟨_, hm, hc⟩ := parametric_optimizer_local P.cost_cont P.strong
    P.joint_cont P.convex hs
  exact ⟨hm.mono fun _ h => ⟨h.1, isMinOn_iff.mpr h.2⟩, hc⟩

variable {c : X → W → ℝ} {cc : Continuous (fun p : X × W => c p.1 p.2)}
    {cv : ∀ x, ConvexOn ℝ univ (fun w => -c x w)}

omit [FiniteDimensional ℝ W] in
theorem barrier_domain (x : X) :
    (P.addBarrier c cc cv).domain x = filtered (P.domain x) (c x) := by
  ext w
  simp [addBarrier, domain, Feasible, filtered, Fin.forall_fin_succ, and_comm]

omit [FiniteDimensional ℝ W] in
theorem base_slater_of_filtered {p : X} (h : (P.addBarrier c cc cv).slater p) :
    P.slater p := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, fun j => hw j.succ⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Strict feasibility and different plant velocities at p suffice for local
activity. Both optimizer continuity statements are discharged internally. -/
theorem local_activity {p : X}
    (hs : (P.addBarrier c cc cv).slater p)
    {plant : W → E}
    (undesirable : plant ((P.addBarrier c cc cv).decision p) ≠ plant (P.decision p)) :
    ∀ᶠ x in 𝓝 p, c x ((P.addBarrier c cc cv).decision x) = 0 := by
  obtain ⟨hf, cf⟩ := (P.addBarrier c cc cv).local_decision hs
  obtain ⟨hn, cn⟩ := P.local_decision (P.base_slater_of_filtered hs)
  apply eventually_active (K := P.domain) (L := P.cost) (w := P.decision) _ hn _ _ cf cn
    (fun h => undesirable (congrArg plant h))
  · filter_upwards [hf] with x hx
    rw [← P.barrier_domain]
    exact hx
  · apply Eventually.of_forall
    intro x
    obtain ⟨μ, hμ, hL⟩ := P.strong x
    exact (hL.strictConvexOn hμ).subset (subset_univ _) (feasible_convex (P.convex x))
  · exact .of_forall (fun x => (cc.comp (continuous_const.prodMk continuous_id)).continuousAt)

end Program


end
end CBFIndependence
