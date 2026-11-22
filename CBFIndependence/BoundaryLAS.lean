import CBFIndependence.CompactContinuation
import CBFIndependence.Reference
import CBFIndependence.Invariant
import CBFIndependence.UniformReference
import CBFIndependence.Recenter

namespace CBFIndependence
open Set Metric Filter Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Reduction to the boundary for continuous closed-loop fields. The finite
time return estimates follow from LAS of the restricted maximal solutions. -/
theorem centered_boundary_las {V Q Z : Set E} {F : E → E} {h : E → ℝ} {α : ℝ → ℝ}
    (ov : IsOpen V) (origin : (0:E) ∈ V) (compactQ : IsCompact Q) (vq : V ⊆ Q)
    (hc : ContinuousOn h Q) (hzero : h 0 = 0) (closedZ : IsClosed Z)
    (zeros : ∀ x ∈ V, h x = 0 ↔ x ∈ Z) (cont : ContinuousOn F V)
    (dh : ∀ x ∈ V, DifferentiableAt ℝ h x)
    (act : ∀ x ∈ V, fderiv ℝ h x (F x) = -α (h x))
    {ρ : WithTop ℝ} (values : MapsTo h V (barrierInterval ρ)) (cα : ContinuousOn α (barrierInterval ρ))
    (restore : ∀ r ∈ barrierInterval ρ, r ≠ 0 → 0 < r * α r) :
    StrongLAS (MaximalSolutionsOn F V) 0 ↔ StrongLAS (MaximalSolutionsOn F (V ∩ Z)) 0 := by
  have sign x (hx : x ∈ V) : 0 ≤ h x * α (h x) := by
    by_cases he : h x = 0
    · simp [he]
    · exact (restore _ (values hx) he).le
  constructor
  · intro full
    exact full.mono (maximalOn_inter_subset (fun c hs hz t ht => (zeros _ (hs.2 t ht)).mp
      ((normal_sublevel_invariance dh act sign hs).1 t ht ((zeros _ (hs.2 0 c.zero_inDomain)).mpr hz))))
  intro boundary
  obtain ⟨R',hR',hball⟩ := Metric.mem_nhds_iff.mp (ov.mem_nhds origin)
  let Rbar := R' / 2
  have hR : 0 < Rbar := half_pos hR'
  have ballV : closedBall (0:E) Rbar ⊆ V := (closedBall_subset_ball (half_lt_self hR')).trans hball
  let B : E × ℝ → E := fun y => F y.1
  let C := (fun x : E => (x,h x)) '' Q
  let trajectories := GraphLiftFamily h (MaximalSolutionsOn F V)
  have hC : IsClosed C := (compactQ.image_of_continuousOn (continuousOn_id.prodMk hc)).isClosed
  have hB : ContinuousOn B (closedBall 0 Rbar ×ˢ Icc (-1:ℝ) 1) :=
    cont.comp continuous_fst.continuousOn (fun x hx => ballV hx.1)
  have hrel : ObservationRelation trajectories C := by
    rintro _ ⟨c,hm,rfl⟩ t ht
    exact ⟨_,vq (hm.1.2 t ht),rfl⟩
  have hdyn : ObservationDynamics trajectories B := observationDynamics_graphLift_on (fun _ _ => rfl)
  have hEq : NormalEquation trajectories α := normalEquation_graphLift_on
    (fun x hx => (dh x hx).hasFDerivAt) act
  have range : ∀ c ∈ trajectories, ∀ t, c.InDomain t → (c.curve t).2 ∈ barrierInterval ρ := by
    rintro _ ⟨c,hm,rfl⟩ t ht; exact values (hm.1.2 t ht)
  have estimates (e : ℝ) (he : 0 < e) (heR : e ≤ Rbar) :
      ∃ a > 0, a < e ∧ ∀ d > 0, ∃ T > 0, ReferenceEstimate B C (closedBall 0 a) T e d := by
    obtain ⟨a,ha,hae,htimes⟩ := strongLAS_on_inter_uniform_reference
      (F := F) (V := V) (Bdy := Z) closedZ (cont.mono inter_subset_left)
      (Rbar := Rbar) (ball_subset_closedBall.trans ballV) boundary e he heR
    refine ⟨a,ha,hae,?_⟩
    intro d hd
    obtain ⟨T,hT,hest⟩ := htimes d hd
    refine ⟨T,hT,?_⟩
    have rtest := reference_block_test (h := h) (B := B) (T := T) (d := d)
      (Q := closedBall 0 e) hT (cont.mono (inter_subset_left (t := Z)))
      (fun x hx hz => ⟨⟨ballV (closedBall_subset_closedBall heR hx),
        (zeros x (ballV (closedBall_subset_closedBall heR hx))).mp hz⟩,rfl⟩)
      (A := closedBall 0 a) (fun x hx => (show ‖x‖ ≤ a by simpa using hx).trans_lt hae)
      (fun c hm hi _ => hest c hm hi)
    intro L hL g hg hq hdg hi
    exact rtest L hL g hg (fun t ht => by
      obtain ⟨x,_,hh⟩ := (hq t ht).2
      have h₁ : x = g t := congrArg Prod.fst hh
      have h₂ : h x = 0 := congrArg Prod.snd hh
      exact ⟨(hq t ht).1,h₁ ▸ h₂⟩) hdg hi
  obtain ⟨r,hr,hrR,endpoint⟩ := estimates Rbar hR le_rfl
  have blocks := tangentBlockProperty_of_referenceEstimates hdyn hrel hR zero_lt_one hB hC (by
    intro e he heR
    obtain ⟨a,ha,hae,ht⟩ := estimates e he heR
    exact ⟨a,ha,hae,ht a ha⟩)
  have ends := tangentEndpointProperty_of_referenceEstimates hdyn hrel zero_lt_one hrR hB hC endpoint
  have continuation : BoundedContinuation trajectories r := by
    rintro _ ⟨c,hm,rfl⟩ trapped
    apply continuousOn_compact_maximal_global ov cont (isCompact_closedBall 0 r)
      ((closedBall_subset_closedBall hrR.le).trans ballV) hm
    intro t ht
    have small := (norm_fst_le ((graphLift h c).curve t)).trans (trapped t ht)
    simpa [graphLift, ForwardCurve.map] using small
  have normals := normalBounds_of_local_equation hEq range cα restore
  have result := strongLAS_of_finite_blocks hr normals.1 blocks continuation normals.2 ends
    (graphLiftFamily_globalShiftClosed (maximalSolutionsOn_globalShiftClosed F V))
  apply (strongLAS_graphLift_iff (dh 0 origin).continuousAt).mp
  rw [hzero]
  exact result

/-- The same reduction at an arbitrary equilibrium. The compact set Q is a
local neighborhood on which the observation is continuous. -/
theorem boundary_las_at {V Q Z : Set E} {F : E → E} {h : E → ℝ} {α : ℝ → ℝ} {p : E}
    (ov : IsOpen V) (hp : p ∈ V) (compactQ : IsCompact Q) (vq : V ⊆ Q)
    (hc : ContinuousOn h Q) (hzero : h p = 0) (closedZ : IsClosed Z)
    (zeros : ∀ x ∈ V, h x = 0 ↔ x ∈ Z) (cont : ContinuousOn F V)
    (dh : ∀ x ∈ V, DifferentiableAt ℝ h x)
    (act : ∀ x ∈ V, fderiv ℝ h x (F x) = -α (h x))
    {ρ : WithTop ℝ} (values : MapsTo h V (barrierInterval ρ)) (cα : ContinuousOn α (barrierInterval ρ))
    (restore : ∀ r ∈ barrierInterval ρ, r ≠ 0 → 0 < r * α r) :
    StrongLAS (MaximalSolutionsOn F V) p ↔ StrongLAS (MaximalSolutionsOn F (V ∩ Z)) p := by
  let tr := fun x : E => x+p
  have htr : Continuous tr := continuous_id.add continuous_const
  let Q' := (fun x : E => x-p) '' Q
  have into : MapsTo tr Q' Q := by rintro _ ⟨x,hx,rfl⟩; simpa [tr] using hx
  have sub : tr ⁻¹' V ⊆ Q' := fun x hx => ⟨x+p,vq hx,add_sub_cancel_right _ _⟩
  have hd (x : E) (hx : x ∈ tr ⁻¹' V) : HasFDerivAt (h ∘ tr) (fderiv ℝ h (tr x)) x := by
    have ht : HasFDerivAt tr (ContinuousLinearMap.id ℝ E) x := (hasFDerivAt_id x).add_const p
    simpa using ((dh _ hx).hasFDerivAt.comp x ht)
  have hh := centered_boundary_las (V := tr ⁻¹' V) (Q := Q') (Z := tr ⁻¹' Z)
    (F := F ∘ tr) (h := h ∘ tr) (ov.preimage htr) (by simpa [tr] using hp)
    (compactQ.image (continuous_id.sub continuous_const)) sub (hc.comp htr.continuousOn into)
    (by simpa [tr] using hzero) (closedZ.preimage htr) (fun x hx => zeros _ hx)
    (cont.comp htr.continuousOn (fun _ hx => hx)) (fun x hx => (hd x hx).differentiableAt)
    (fun x hx => by rw [(hd x hx).fderiv]; exact act _ hx) (fun _ hx => values hx) cα restore
  exact (recenter_las_iff (F := F) (D := V) p).symm.trans
    (hh.trans (recenter_las_iff (F := F) (D := V ∩ Z) p))

end
end CBFIndependence
