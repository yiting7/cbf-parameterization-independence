import CBFIndependence.Cascade
import CBFIndependence.Scalar

namespace CBFIndependence
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Invariance for every classical solution, including when the scalar
equation is non-Lipschitz. A zero reached at any time cannot be left. -/
theorem normal_sublevel_invariance {F : E → E} {V : Set E} {h : E → ℝ} {α : ℝ → ℝ}
    (dh : ∀ x ∈ V, DifferentiableAt ℝ h x)
    (active : ∀ x ∈ V, fderiv ℝ h x (F x) = -α (h x))
    (sign : ∀ x ∈ V, 0 ≤ h x * α (h x)) {c : ForwardCurve E} (hc : SolvesODEOn F V c) :
    (∀ t, c.InDomain t → h (c.curve 0) = 0 → h (c.curve t) = 0) ∧
    (∀ t, c.InDomain t → 0 ≤ h (c.curve 0) → 0 ≤ h (c.curve t)) := by
  let r := h ∘ c.curve
  have der t (ht : c.InDomain t) : HasDerivWithinAt r (-α (r t)) (Ici 0) t := by
    change HasDerivWithinAt r (-α (h (c.curve t))) (Ici 0) t
    rw [← active _ (hc.2 t ht)]
    exact (dh _ (hc.2 t ht)).hasFDerivAt.comp_hasDerivWithinAt t (hc.1 t ht)
  have anti t (ht : c.InDomain t) : AntitoneOn (fun s => r s * r s) (Icc 0 t) :=
    normal_sq_antitone (convex_Icc _ _) (fun s hs =>
      (der s (c.inDomain_mono ht hs.1 hs.2)).mono Icc_subset_Ici_self)
      (fun s hs => sign _ (hc.2 s (c.inDomain_mono ht hs.1 hs.2)))
  have stay t (ht : c.InDomain t) s (hs : s ∈ Icc 0 t) (hz : r s = 0) : r t = 0 := by
    have hh := anti t ht hs (right_mem_Icc.mpr ht.1) hs.2
    change r t * r t ≤ r s * r s at hh
    rw [hz,zero_mul] at hh
    nlinarith [sq_nonneg (r t)]
  refine ⟨fun t ht hz => stay t ht 0 (left_mem_Icc.mpr ht.1) hz, ?_⟩
  intro t ht h₀
  change 0 ≤ r t
  by_contra! hn
  have cont : ContinuousOn r (Icc 0 t) := fun s hs =>
    (der s (c.inDomain_mono ht hs.1 hs.2)).continuousWithinAt.mono Icc_subset_Ici_self
  obtain ⟨s,hs,hz⟩ := intermediate_value_Icc' ht.1 cont ⟨hn.le,h₀⟩
  exact hn.ne (stay t ht s hs hz)

/-- If solutions initially in Z stay there, a maximal solution in V∩Z
is already maximal in V; no uniqueness is needed. -/
theorem maximalOn_inter_subset {F : E → E} {V Z : Set E}
    (inv : ∀ c, SolvesODEOn F V c → c.curve 0 ∈ Z → ∀ t, c.InDomain t → c.curve t ∈ Z) :
    MaximalSolutionsOn F (V ∩ Z) ⊆ MaximalSolutionsOn F V := by
  intro c hc
  refine ⟨⟨hc.1.1,fun t ht => (hc.1.2 t ht).1⟩,?_⟩
  intro d hd he
  apply hc.2 d _ he
  have hz : d.curve 0 ∈ Z := by rw [he.2 0 c.zero_inDomain]; exact (hc.1.2 0 c.zero_inDomain).2
  exact ⟨hd.1,fun t ht => ⟨hd.2 t ht,inv d hd hz t ht⟩⟩

theorem maximalOn_eq_of_eqOn {F G : E → E} {D : Set E} (eq : EqOn F G D) :
    MaximalSolutionsOn F D = MaximalSolutionsOn G D := by
  have sol {A B : E → E} (ab : EqOn A B D) {c : ForwardCurve E} (hc : SolvesODEOn A D c) :
      SolvesODEOn B D c := ⟨fun t ht => by rw [← ab (hc.2 t ht)]; exact hc.1 t ht,hc.2⟩
  ext c
  exact ⟨fun hc => ⟨sol eq hc.1,fun d hd he => hc.2 d (sol eq.symm hd) he⟩,
    fun hc => ⟨sol eq.symm hc.1,fun d hd he => hc.2 d (sol eq hd) he⟩⟩

end CBFIndependence
