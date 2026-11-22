import CBFIndependence.LocalModel

namespace CBFIndependence
open Set Filter Topology Geometry Optimization
noncomputable section

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ}

omit [NormedSpace ℝ E] in
@[simp] theorem ambientField_val (F : U → E) (x : U) : ambientField F (x:E) = F x := by
  classical
  simp [ambientField, x.property]

omit [NormedSpace ℝ E] in
theorem ambientField_continuousAt (oU : IsOpen U) {F : U → E} {x : U}
    (hc : ContinuousAt F x) : ContinuousAt (ambientField F) (x:E) := by
  apply (continuousWithinAt_iff_continuousAt_restrict _ x.property).mpr _ |>.continuousAt (oU.mem_nhds x.property)
  simpa only [restrict_def, ambientField_val] using hc

omit [NormedSpace ℝ E] [FiniteDimensional ℝ W] in
theorem Program.eventually_slater (P : Program U W q) {p : U} (hs : P.slater p) :
    ∀ᶠ x in 𝓝 p, P.slater x := by
  obtain ⟨w,hw⟩ := hs
  exact (strictlyFeasible_eventually (fun j => ((P.joint_cont j).comp
    (continuous_id.prodMk continuous_const)).continuousAt) hw).mono fun x hx => ⟨w,hx⟩

namespace Barrier
variable (H : Barrier U) (oU : IsOpen U) (A : Plant U W) (P : Program U W q)

include oU in
theorem deriv_at (x : U) : HasFDerivAt H.h (H.normal x) (x:E) :=
  ((H.smooth.differentiableOn le_rfl x x.property).differentiableAt
    (oU.mem_nhds x.property)).hasFDerivAt

theorem field_cont_at {x : U} (hs : (H.program oU A P).slater x) :
    ContinuousAt (H.field oU A P) x :=
  A.drift_cont.continuousAt.add (A.input_cont.continuousAt.clm_apply
    ((H.program oU A P).local_decision hs).2)
end Barrier

theorem germ_superlevel {S : Set E} {H : Barrier U} (oU : IsOpen U)
    (same : ∀ x ∈ U, 0 ≤ H.h x ↔ x ∈ S) (x : U) : superlevel H.h =ᶠ[𝓝 (x:E)] S := by
  filter_upwards [oU.mem_nhds x.property] with y hy
  exact propext (same y hy)

/-- A single open neighborhood works for both optimizers. Their fields agree
on the boundary there. In particular the common boundary field is tangent. -/
theorem common_local_dynamics (oU : IsOpen U) (S : Set E) (H J : Barrier U)
    (A : Plant U W) (P : Program U W q) (p : U)
    (sameH : ∀ x ∈ U, 0 ≤ H.h x ↔ x ∈ S)
    (sameJ : ∀ x ∈ U, 0 ≤ J.h x ↔ x ∈ S)
    (sH : (H.program oU A P).slater p) (sJ : (J.program oU A P).slater p)
    (eqH : H.field oU A P p = 0) (nom : A.velocity p (P.decision p) ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ (p:E) ∈ V ∧ V ⊆ U ∧
      BarrierDynamics (ambientField (H.field oU A P)) H.h (H.α ∘ H.h) V S ∧
      BarrierDynamics (ambientField (J.field oU A P)) J.h (J.α ∘ J.h) V S ∧
      EqOn (ambientField (H.field oU A P)) (ambientField (J.field oU A P)) (V ∩ frontier S) := by
  obtain ⟨_, _, _, nH,nJ,_,aH,aJ⟩ := equilibrium_and_activity oU S H J A P p sameH sameJ sH sJ eqH nom
  have reg (B : Barrier U) (n : B.normal p ≠ 0) : ∀ᶠ x in 𝓝 p, B.normal x ≠ 0 :=
    (B.normal_cont oU).continuousAt.eventually_ne n
  let good : Set U := {x | (H.program oU A P).slater x ∧ (J.program oU A P).slater x ∧
    H.normal x ≠ 0 ∧ J.normal x ≠ 0 ∧ H.normal x (H.field oU A P x) = -H.offset x ∧
    J.normal x (J.field oU A P x) = -J.offset x}
  have hgood : good ∈ 𝓝 p := by
    filter_upwards [(H.program oU A P).eventually_slater sH, (J.program oU A P).eventually_slater sJ,
      reg H nH,reg J nJ,aH,aJ] with x h j nh nj ah aj
    exact ⟨h,j,nh,nj,ah,aj⟩
  obtain ⟨v,hv,ov,pv⟩ := mem_nhds_iff.mp hgood
  let V : Set E := Subtype.val '' v
  have incl : V ⊆ U := by rintro _ ⟨x,_,rfl⟩; exact x.property
  have zi (B : Barrier U) (same : ∀ x ∈ U, 0 ≤ B.h x ↔ x ∈ S)
      (x : U) (nx : B.normal x ≠ 0) : B.h x = 0 ↔ (x:E) ∈ frontier S := by
    rw [← mem_frontier_iff_of_eventuallyEq (germ_superlevel oU same x)]
    exact ⟨fun hx => mem_frontier_of_regular_zero (B.deriv_at oU x) hx nx,
      zero_of_mem_frontier_of_continuousAt (B.deriv_at oU x).continuousAt⟩
  have dyn (B : Barrier U) (same : ∀ x ∈ U, 0 ≤ B.h x ↔ x ∈ S)
      (data : ∀ x ∈ v, (B.program oU A P).slater x ∧ B.normal x ≠ 0 ∧
        B.normal x (B.field oU A P x) = -B.offset x) :
      BarrierDynamics (ambientField (B.field oU A P)) B.h (B.α ∘ B.h) V S := by
    constructor
    · rintro _ ⟨x,hx,rfl⟩
      exact (ambientField_continuousAt oU (B.field_cont_at oU A P (data x hx).1)).continuousWithinAt
    · rintro _ ⟨x,hx,rfl⟩; exact zi B same x (data x hx).2.1
    · rintro _ ⟨x,hx,rfl⟩; simpa only [ambientField_val] using (data x hx).2.2
  refine ⟨V, oU.isOpenMap_subtype_val v ov, ⟨p,pv,rfl⟩, incl,
    dyn H sameH (fun x hx => ⟨(hv hx).1,(hv hx).2.2.1,(hv hx).2.2.2.2.1⟩),
    dyn J sameJ (fun x hx => ⟨(hv hx).2.1,(hv hx).2.2.2.1,(hv hx).2.2.2.2.2⟩), ?_⟩
  rintro _ ⟨⟨x,hx,rfl⟩,bd⟩
  have nh := (hv hx).2.2.1
  have nj := (hv hx).2.2.2.1
  have zh := (zi H sameH x nh).mpr bd
  have zj := (zi J sameJ x nj).mpr bd
  obtain ⟨k,hk,hn⟩ := normals_positive_multiple_of_eventuallyEq (H.deriv_at oU x) (J.deriv_at oU x)
    zh zj ((germ_superlevel oU sameH x).trans (germ_superlevel oU sameJ x).symm) nh nj
  have dom : filtered (P.domain x) (H.cbf A x) = filtered (P.domain x) (J.cbf A x) := by
    ext w
    simp [filtered, Barrier.cbf, residual, Barrier.offset, zh, zj, H.zero, J.zero, hn, hk]
  simp only [ambientField_val, Barrier.field, Barrier.decision_eq, dom]

end
end CBFIndependence
