import CBFIndependence.Equilibrium

namespace CBFIndependence
open Set Filter Topology Geometry Optimization
noncomputable section

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ}

namespace Barrier
variable (H : Barrier U) (oU : IsOpen U) (A : Plant U W) (P : Program U W q)

omit [FiniteDimensional ℝ W] in
theorem feasible_eq (x : U) :
    (H.program oU A P).domain x = filtered (P.domain x) (H.cbf A x) :=
  P.barrier_domain x

omit [FiniteDimensional ℝ W] in
theorem decision_eq (x : U) :
    (H.program oU A P).decision x = optimizer (P.cost x) (filtered (P.domain x) (H.cbf A x)) := by
  unfold Program.decision
  rw [H.feasible_eq]
  rfl

omit [FiniteDimensional ℝ W] in
theorem strict_cbf_test {p : U} (hs : (H.program oU A P).slater p) :
    ∃ s ∈ P.domain p, 0 < H.cbf A p s := by
  obtain ⟨w, hw⟩ := hs
  refine ⟨w, fun j => (hw j.succ).le, ?_⟩
  have hw₀ := hw 0
  change - H.cbf A p w < 0 at hw₀
  exact neg_lt_zero.mp hw₀

theorem local_normal_equation {p : U} (hs : (H.program oU A P).slater p)
    (undes : H.field oU A P p ≠ A.velocity p (P.decision p)) :
    ∀ᶠ x in 𝓝 p, H.normal x (H.field oU A P x) = - H.offset x := by
  have h := P.local_activity hs undes
  exact h.mono fun x hx => eq_neg_of_add_eq_zero_left hx
end Barrier

/-- All pointwise optimizer, activity, and geometric premises in this result
are derived from the raw program, the two Slater witnesses, and undesirability. -/
theorem equilibrium_and_activity (oU : IsOpen U) (S : Set E) (H J : Barrier U)
    (A : Plant U W) (P : Program U W q) (p : U)
    (sameH : ∀ x ∈ U, 0 ≤ H.h x ↔ x ∈ S)
    (sameJ : ∀ x ∈ U, 0 ≤ J.h x ↔ x ∈ S)
    (sH : (H.program oU A P).slater p) (sJ : (J.program oU A P).slater p)
    (eqH : H.field oU A P p = 0) (nom : A.velocity p (P.decision p) ≠ 0) :
    (p:E) ∈ frontier S ∧ H.h p = 0 ∧ J.h p = 0 ∧ H.normal p ≠ 0 ∧ J.normal p ≠ 0 ∧
      J.field oU A P p = 0 ∧
      (∀ᶠ x in 𝓝 p, H.normal x (H.field oU A P x) = - H.offset x) ∧
      (∀ᶠ x in 𝓝 p, J.normal x (J.field oU A P x) = - J.offset x) := by
  have baseS := P.base_slater_of_filtered sH
  have min₀ := (P.local_decision baseS).1.self_of_nhds
  have min₁ := ((H.program oU A P).local_decision sH).1.self_of_nhds
  have eH := eqH
  unfold Barrier.field at eH
  rw [H.decision_eq] at eH
  rw [H.feasible_eq, H.decision_eq] at min₁
  have hn (B : Barrier U) : HasFDerivAt B.h (B.normal p) (p:E) :=
    ((B.smooth.differentiableOn le_rfl p p.property).differentiableAt
      (oU.mem_nhds p.property)).hasFDerivAt
  have ev (B : Barrier U) (h : ∀ x ∈ U, 0 ≤ B.h x ↔ x ∈ S) :
      superlevel B.h =ᶠ[𝓝 (p:E)] S := by
    filter_upwards [oU.mem_nhds p.property] with x hx
    exact propext (h x hx)
  obtain ⟨μ,hμ,hc⟩ := P.strong p
  obtain ⟨bd,h₁,h₂,n₁,n₂,eJ⟩ := common_undesirable_equilibrium
    ((hc.strictConvexOn hμ).subset (subset_univ _) (feasible_convex (P.convex p)))
    (hn H) (hn J) (ev H sameH) (ev J sameJ) H.zero J.zero
    (H.restoring _ (H.range_ok p.property))
    (A := A.velocity p) (continuous_const.add (A.input p).continuous)
    (H.strict_cbf_test oU A P sH) (J.strict_cbf_test oU A P sJ) min₀ min₁ eH nom
  have eqJ : J.field oU A P p = 0 := by unfold Barrier.field; rw [J.decision_eq]; exact eJ
  exact ⟨bd,h₁,h₂,n₁,n₂,eqJ,
    H.local_normal_equation oU A P sH (eqH ▸ Ne.symm nom),
    J.local_normal_equation oU A P sJ (eqJ ▸ Ne.symm nom)⟩

end
end CBFIndependence
