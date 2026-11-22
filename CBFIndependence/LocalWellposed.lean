import CBFIndependence.LocalGerm
import CBFIndependence.CompactContinuation

/-!
# Local well-posedness of the actual controller programs

The nominal program and the two programs obtained by adding CBF constraints
have unique optimizers on one common open neighborhood. Their actual chosen
decisions solve the programs and are continuous at every point there. All of
these facts follow from the original program data and two Slater witnesses at
the distinguished point; optimizer continuity is not an assumption.
-/

noncomputable section

namespace CBFIndependence

open Set Filter Topology Geometry Optimization

section ParameterSpace

variable {X W : Type*} [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] {q : ℕ}

namespace Program

/-- Strong convexity and Slater discharge all three well-posedness conclusions. -/
theorem wellposedAt_of_slater (P : Program X W q) {x : X} (hs : P.slater x) :
    P.WellposedAt x := by
  obtain ⟨hnear, hcont⟩ := P.local_decision hs
  have hsolve := hnear.self_of_nhds
  obtain ⟨m, hm, hstrong⟩ := P.strong x
  have hstrict := (hstrong.strictConvexOn hm).subset (subset_univ _)
    (feasible_convex (P.convex x))
  refine ⟨⟨P.decision x, hsolve, ?_⟩, hsolve, hcont⟩
  intro y hy
  exact hstrict.eq_of_isMinOn hy.2 hsolve.2 hy.1 hsolve.1

end Program
end ParameterSpace

section LocalState

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ}

omit [FiniteDimensional ℝ W] in
theorem ControllerProgramsWellposedOn.mono {oU : IsOpen U} {H J : Barrier U}
    {A : Plant U W} {P : Program U W q} {V V' : Set E}
    (h : ControllerProgramsWellposedOn oU H J A P V) (hsub : V' ⊆ V) :
    ControllerProgramsWellposedOn oU H J A P V' :=
  ⟨fun x hx => h.nominal x (hsub hx), fun x hx => h.first x (hsub hx),
    fun x hx => h.second x (hsub hx)⟩

omit [FiniteDimensional ℝ W] in
/-- Continuity of the actual nominal and filtered plant fields follows from
the optimizer conclusion; it is not an additional regularity assumption. -/
theorem ControllerProgramsWellposedOn.fields_continuous {oU : IsOpen U}
    {H J : Barrier U} {A : Plant U W} {P : Program U W q} {V : Set E}
    (hw : ControllerProgramsWellposedOn oU H J A P V) (hVU : V ⊆ U) :
    ContinuousOn (ambientField (fun x => A.velocity x (P.decision x))) V ∧
      ContinuousOn (ambientField (H.field oU A P)) V ∧
      ContinuousOn (ambientField (J.field oU A P)) V := by
  have cont {k : ℕ} (Q : Program U W k)
      (hq : ∀ x : U, (x : E) ∈ V → Q.WellposedAt x) :
      ContinuousOn (ambientField (fun x => A.velocity x (Q.decision x))) V := by
    intro x hx
    let xU : U := ⟨x, hVU hx⟩
    have ha : ContinuousAt (fun y => A.velocity y (Q.decision y)) xU :=
      A.drift_cont.continuousAt.add
        (A.input_cont.continuousAt.clm_apply (hq xU hx).continuous)
    exact (ambientField_continuousAt oU ha).continuousWithinAt
  exact ⟨cont P hw.nominal, cont (H.program oU A P) hw.first,
    cont (J.program oU A P) hw.second⟩

omit [FiniteDimensional ℝ W] in
/-- Every state of the common open neighborhood has a maximal forward solution
for each of the three actual fields. Existence follows from continuity and
Peano; no uniqueness of the ODE is asserted. -/
theorem ControllerProgramsWellposedOn.exists_maximal_solutions
    [FiniteDimensional ℝ E] {oU : IsOpen U}
    {H J : Barrier U} {A : Plant U W} {P : Program U W q} {V : Set E}
    (hw : ControllerProgramsWellposedOn oU H J A P V)
    (hV : IsOpen V) (hVU : V ⊆ U) {x : E} (hx : x ∈ V) :
    (∃ c : ForwardCurve E,
      MaximalSolutionOn (ambientField (fun y => A.velocity y (P.decision y))) V c ∧
      c.curve 0 = x) ∧
    (∃ c : ForwardCurve E,
      MaximalSolutionOn (ambientField (H.field oU A P)) V c ∧ c.curve 0 = x) ∧
    (∃ c : ForwardCurve E,
      MaximalSolutionOn (ambientField (J.field oU A P)) V c ∧ c.curve 0 = x) := by
  obtain ⟨h₀, h₁, h₂⟩ := hw.fields_continuous hVU
  exact ⟨exists_maximal_solution_on hV h₀ hx,
    exists_maximal_solution_on hV h₁ hx, exists_maximal_solution_on hV h₂ hx⟩

/-- Two Slater witnesses at one point yield a common open neighborhood on which
the nominal and both filtered programs have unique continuous optimizers. No
equilibrium or stability premise is needed for this phase of the argument. -/
theorem common_local_wellposed (oU : IsOpen U) (H J : Barrier U)
    (A : Plant U W) (P : Program U W q) (p : U)
    (sH : (H.program oU A P).slater p) (sJ : (J.program oU A P).slater p) :
    ∃ V : Set E, IsOpen V ∧ (p : E) ∈ V ∧ V ⊆ U ∧
      ControllerProgramsWellposedOn oU H J A P V := by
  let good : Set U := {x | (H.program oU A P).slater x ∧
    (J.program oU A P).slater x}
  have hgood : good ∈ 𝓝 p :=
    ((H.program oU A P).eventually_slater sH).and
      ((J.program oU A P).eventually_slater sJ)
  obtain ⟨v, hv, ov, pv⟩ := mem_nhds_iff.mp hgood
  let V : Set E := Subtype.val '' v
  have incl : V ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hslater : ∀ x : U, (x : E) ∈ V →
      (H.program oU A P).slater x ∧ (J.program oU A P).slater x := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := hx
    have hyx : y = x := Subtype.ext heq
    subst y
    exact hv hy
  refine ⟨V, oU.isOpenMap_subtype_val v ov, ⟨p, pv, rfl⟩, incl, ?_⟩
  constructor
  · intro x hx
    exact P.wellposedAt_of_slater (P.base_slater_of_filtered (hslater x hx).1)
  · intro x hx
    exact (H.program oU A P).wellposedAt_of_slater (hslater x hx).1
  · intro x hx
    exact (J.program oU A P).wellposedAt_of_slater (hslater x hx).2

theorem BarrierDynamics.mono {F : E → E} {h α : E → ℝ} {V V' S : Set E}
    (hd : BarrierDynamics F h α V S) (hsub : V' ⊆ V) :
    BarrierDynamics F h α V' S :=
  ⟨hd.continuous.mono hsub, fun x hx => hd.zero_iff x (hsub hx),
    fun x hx => hd.active x (hsub hx)⟩

/-- The optimizer conclusions and the common boundary dynamics hold on the
same open neighborhood. This is a strengthened interface to `LocalGerm`. -/
theorem common_local_wellposed_dynamics (oU : IsOpen U) (S : Set E)
    (H J : Barrier U) (A : Plant U W) (P : Program U W q) (p : U)
    (sameH : ∀ x ∈ U, 0 ≤ H.h x ↔ x ∈ S)
    (sameJ : ∀ x ∈ U, 0 ≤ J.h x ↔ x ∈ S)
    (sH : (H.program oU A P).slater p) (sJ : (J.program oU A P).slater p)
    (eqH : H.field oU A P p = 0) (nom : A.velocity p (P.decision p) ≠ 0) :
    ∃ V : Set E, IsOpen V ∧ (p : E) ∈ V ∧ V ⊆ U ∧
      ControllerProgramsWellposedOn oU H J A P V ∧
      BarrierDynamics (ambientField (H.field oU A P)) H.h (H.α ∘ H.h) V S ∧
      BarrierDynamics (ambientField (J.field oU A P)) J.h (J.α ∘ J.h) V S ∧
      EqOn (ambientField (H.field oU A P)) (ambientField (J.field oU A P))
        (V ∩ frontier S) := by
  obtain ⟨W₀, oW, pW, WU, hwell⟩ := common_local_wellposed oU H J A P p sH sJ
  obtain ⟨O, oO, pO, OU, hdH, hdJ, heq⟩ :=
    common_local_dynamics oU S H J A P p sameH sameJ sH sJ eqH nom
  refine ⟨W₀ ∩ O, oW.inter oO, ⟨pW, pO⟩,
    inter_subset_left.trans WU, hwell.mono inter_subset_left,
    hdH.mono inter_subset_right, hdJ.mono inter_subset_right, ?_⟩
  exact heq.mono (inter_subset_inter_left (frontier S) inter_subset_right)

end LocalState

end CBFIndependence
