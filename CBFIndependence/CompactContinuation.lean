import CBFIndependence.Continuation
import CBFIndependence.MaximalExtension
import CBFIndependence.Peano

/-!
# Compact-range continuation for maximal forward solutions

This module supplies the genuine continuation argument, retaining lifetimes and
allowing nonunique solutions. Local existence is an explicit analytic premise;
the Peano module discharges it for continuous finite-dimensional vector fields.
-/

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace CBFIndependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local existence with arbitrary starting time at every point of a set. -/
def LocalForwardExistenceOn (F : E → E) (K : Set E) : Prop :=
  ∀ a x, x ∈ K → ∃ b > a, ∃ γ : ℝ → E, γ a = x ∧
    ∀ t ∈ Ico a b, HasDerivWithinAt γ (F (γ t)) (Ici a) t

/-- Local solutions starting in `K` are required to stay in `U`. -/
def LocalForwardExistenceWithin (F : E → E) (U K : Set E) : Prop :=
  ∀ a x, x ∈ K → ∃ b > a, ∃ γ : ℝ → E, γ a = x ∧
    (∀ t ∈ Ico a b, γ t ∈ U) ∧
    ∀ t ∈ Ico a b, HasDerivWithinAt γ (F (γ t)) (Ici a) t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem finite_lifetime_inDomain_iff {c : ForwardCurve E}
    (hf : c.lifetime ≠ ⊤) {t : ℝ} :
    c.InDomain t ↔ t ∈ Ico 0 c.lifetime.toReal := by
  change (0 ≤ t ∧ ENNReal.ofReal t < c.lifetime) ↔
    (0 ≤ t ∧ t < c.lifetime.toReal)
  exact and_congr_right fun ht => ENNReal.ofReal_lt_iff_lt_toReal ht hf

/-- A maximal solution confined to a compact set is global, provided the field
is continuous at that set and each point there admits a local forward solution.
The proof constructs a strictly longer solution when the lifetime is finite. -/
theorem compact_maximal_global_of_local_existence {F : E → E}
    {K : Set E} {c : ForwardCurve E}
    (hK : IsCompact K) (hF : ∀ x ∈ K, ContinuousAt F x)
    (hex : LocalForwardExistenceOn F K)
    (hc : MaximalSolution F c)
    (hinside : ∀ t, c.InDomain t → c.curve t ∈ K) : c.IsGlobal := by
  change c.lifetime = ⊤
  by_contra hf
  let T := c.lifetime.toReal
  have hT : 0 < T := ENNReal.toReal_pos (ne_of_gt c.positive_lifetime) hf
  have hγ : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt c.curve (F (c.curve t)) (Ici 0) t := by
    intro t ht
    exact hc.1 t ((finite_lifetime_inDomain_iff hf).mpr ht)
  have hinside' : ∀ t ∈ Ico 0 T, c.curve t ∈ K := by
    intro t ht
    exact hinside t ((finite_lifetime_inDomain_iff hf).mpr ht)
  obtain ⟨x, hx, hlim⟩ := Continuation.exists_endpoint_of_continuous_field
    hT hK (fun x hx => (hF x hx).continuousWithinAt) hγ hinside'
  obtain ⟨U, hTU, η, hηT, hη⟩ := hex T x hx
  have hU : 0 < U := hT.trans hTU
  let d : ForwardCurve E := {
    curve := Continuation.glueAt c.curve η T
    lifetime := ENNReal.ofReal U
    positive_lifetime := ENNReal.ofReal_pos.mpr hU }
  have hds : SolvesODE F d := by
    intro t ht
    have ht' : t ∈ Ico 0 U :=
      ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff hU).mp ht.2⟩
    exact Continuation.glueAt_solves hT hTU
      (by simpa only [hηT] using hF x hx) hγ hη
      (by simpa only [hηT] using hlim) t ht'
  have heq : ENNReal.ofReal T = c.lifetime := ENNReal.ofReal_toReal hf
  have hlt : c.lifetime < d.lifetime := by
    change c.lifetime < ENNReal.ofReal U
    rw [← heq]
    exact (ENNReal.ofReal_lt_ofReal_iff hU).mpr hTU
  have hdc : d.Extends c := by
    refine ⟨hlt.le, ?_⟩
    intro t ht
    have htT : t < T := ((finite_lifetime_inDomain_iff hf).mp ht).2
    exact if_pos htT
  exact (ne_of_gt hlt) (hc.2 d hds hdc)

/-- The compact continuation theorem with maximality relative to a domain.
The continuing piece is explicitly required to stay in that domain. -/
theorem compact_maximalOn_global_of_local_existence {F : E → E}
    {U K : Set E} {c : ForwardCurve E}
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ∀ x ∈ K, ContinuousAt F x)
    (hex : LocalForwardExistenceWithin F U K)
    (hc : MaximalSolutionOn F U c)
    (hinside : ∀ t, c.InDomain t → c.curve t ∈ K) : c.IsGlobal := by
  change c.lifetime = ⊤
  by_contra hf
  let T := c.lifetime.toReal
  have hT : 0 < T := ENNReal.toReal_pos (ne_of_gt c.positive_lifetime) hf
  have hγ : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt c.curve (F (c.curve t)) (Ici 0) t := by
    intro t ht
    exact hc.1.1 t ((finite_lifetime_inDomain_iff hf).mpr ht)
  have hinside' : ∀ t ∈ Ico 0 T, c.curve t ∈ K := by
    intro t ht
    exact hinside t ((finite_lifetime_inDomain_iff hf).mpr ht)
  obtain ⟨x, hx, hlim⟩ := Continuation.exists_endpoint_of_continuous_field
    hT hK (fun x hx => (hF x hx).continuousWithinAt) hγ hinside'
  obtain ⟨Utime, hTU, η, hηT, hηU, hη⟩ := hex T x hx
  have hUtime : 0 < Utime := hT.trans hTU
  let d : ForwardCurve E := {
    curve := Continuation.glueAt c.curve η T
    lifetime := ENNReal.ofReal Utime
    positive_lifetime := ENNReal.ofReal_pos.mpr hUtime }
  have hdom : ∀ t, d.InDomain t → t ∈ Ico 0 Utime := by
    intro t ht
    exact ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff hUtime).mp ht.2⟩
  have hds : SolvesODEOn F U d := by
    refine ⟨?_, ?_⟩
    · intro t ht
      exact Continuation.glueAt_solves hT hTU
        (by simpa only [hηT] using hF x hx) hγ hη
        (by simpa only [hηT] using hlim) t (hdom t ht)
    · intro t ht
      by_cases htT : t < T
      · have hin := hKU (hinside' t ⟨ht.1, htT⟩)
        simpa only [d, Continuation.glueAt, if_pos htT] using hin
      · have hin := hηU t ⟨le_of_not_gt htT, (hdom t ht).2⟩
        simpa only [d, Continuation.glueAt, if_neg htT] using hin
  have heq : ENNReal.ofReal T = c.lifetime := ENNReal.ofReal_toReal hf
  have hlt : c.lifetime < d.lifetime := by
    change c.lifetime < ENNReal.ofReal Utime
    rw [← heq]
    exact (ENNReal.ofReal_lt_ofReal_iff hUtime).mpr hTU
  have hdc : d.Extends c := by
    refine ⟨hlt.le, ?_⟩
    intro t ht
    have htT : t < T := ((finite_lifetime_inDomain_iff hf).mp ht).2
    exact if_pos htT
  exact (ne_of_gt hlt) (hc.2 d hds hdc)

/-- Stability confines all sufficiently close maximal solutions to a compact
neighborhood, and compact continuation then makes them all global. -/
theorem stable_maximalOn_eventually_global_of_compact_nhds {F : E → E}
    {U K : Set E} {p : E}
    (hK : IsCompact K) (hKU : K ⊆ U) (hKn : K ∈ 𝓝 p)
    (hF : ∀ x ∈ K, ContinuousAt F x)
    (hex : LocalForwardExistenceWithin F U K)
    (hs : StrongStable (MaximalSolutionsOn F U) p) :
    ∃ δ > 0, ∀ c ∈ MaximalSolutionsOn F U,
      dist (c.curve 0) p < δ → c.IsGlobal := by
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp hKn
  obtain ⟨δ, hδ, hδspec⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro c hc hi
  apply compact_maximalOn_global_of_local_existence hK hKU hF hex hc
  intro t ht
  exact hεK (hδspec c hc hi t ht)

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Continuous finite-dimensional fields satisfy the compact continuation
theorem by Peano existence. -/
theorem continuous_compact_maximal_global {F : E → E}
    {K : Set E} {c : ForwardCurve E}
    (hF : Continuous F) (hK : IsCompact K)
    (hc : MaximalSolution F c)
    (hinside : ∀ t, c.InDomain t → c.curve t ∈ K) : c.IsGlobal := by
  apply compact_maximal_global_of_local_existence hK
    (fun _ _ => hF.continuousAt) ?_ hc hinside
  intro a x _
  exact continuous_exists_local_forward_solution hF a x

/-- No continuity outside the open domain is needed for compact continuation
of solutions maximal within that domain. -/
theorem continuousOn_compact_maximal_global {F : E → E}
    {U K : Set E} {c : ForwardCurve E}
    (hU : IsOpen U) (hF : ContinuousOn F U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hc : MaximalSolutionOn F U c)
    (hinside : ∀ t, c.InDomain t → c.curve t ∈ K) : c.IsGlobal := by
  apply compact_maximalOn_global_of_local_existence hK hKU
    (fun x hx => (hF x (hKU hx)).continuousAt (hU.mem_nhds (hKU hx))) ?_ hc hinside
  intro a x hx
  exact continuousOn_exists_local_forward_solution hU hF a (hKU hx)

/-- On an open finite-dimensional domain, strong stability of a continuous
field already guarantees forward completeness for every sufficiently close
maximal solution, even when local uniqueness fails. -/
theorem continuousOn_strongStable_eventually_global {F : E → E}
    {U : Set E} {p : E}
    (hU : IsOpen U) (hF : ContinuousOn F U) (hp : p ∈ U)
    (hs : StrongStable (MaximalSolutionsOn F U) p) :
    ∃ δ > 0, ∀ c ∈ MaximalSolutionsOn F U,
      dist (c.curve 0) p < δ → c.IsGlobal := by
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  have hKU : Metric.closedBall p (R / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRU
  apply stable_maximalOn_eventually_global_of_compact_nhds
    (isCompact_closedBall p (R / 2)) hKU
    (Metric.closedBall_mem_nhds p (half_pos hR))
    (fun x hx => (hF x (hKU hx)).continuousAt (hU.mem_nhds (hKU hx))) ?_ hs
  intro a x hx
  exact continuousOn_exists_local_forward_solution hU hF a (hKU hx)

/-- The maximal-solution family of a continuous field on an open domain is
nonempty at every point of that domain. This rules out a vacuous stability
interpretation caused by quantifying over a nonexistent solution family. -/
theorem exists_maximal_solution_on {F : E → E} {U : Set E} {x : E}
    (hU : IsOpen U) (hF : ContinuousOn F U) (hx : x ∈ U) :
    ∃ c : ForwardCurve E, MaximalSolutionOn F U c ∧ c.curve 0 = x := by
  obtain ⟨b, hb, γ, hγ0, hγU, hγ⟩ :=
    continuousOn_exists_local_forward_solution hU hF 0 hx
  let c : ForwardCurve E := {
    curve := γ
    lifetime := ENNReal.ofReal b
    positive_lifetime := ENNReal.ofReal_pos.mpr hb }
  have hdom : ∀ t, c.InDomain t → t ∈ Ico 0 b := by
    intro t ht
    exact ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff hb).mp ht.2⟩
  have hc : SolvesODEOn F U c :=
    ⟨fun t ht => hγ t (hdom t ht), fun t ht => hγU t (hdom t ht)⟩
  obtain ⟨d, hdc, hd⟩ := MaximalExtension.exists_maximal_extension_on hc
  exact ⟨d, hd, (hdc.2 0 c.zero_inDomain).trans hγ0⟩

end FiniteDimensional

end CBFIndependence
