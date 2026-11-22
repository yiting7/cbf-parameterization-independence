import CBFIndependence.Cascade
import Mathlib.Order.Zorn
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extension of every solution segment to a maximal solution

This is a Zorn argument on the actual forward-solution curves, ordered by
extension. The order is only a preorder because values outside the lifetime
do not matter. No uniqueness or local Lipschitz assumption is used.
-/

noncomputable section

open Set Filter
open scoped Topology ENNReal

namespace CBFIndependence.MaximalExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance extensionPreorder : Preorder (ForwardCurve E) where
  le c d := d.Extends c
  le_refl c := c.extends_refl
  le_trans _ _ _ hcd hde := ForwardCurve.extends_trans hde hcd

/-- The lifetime supremum and consistent union of a nonempty chain. -/
def chainUpper (S : Set (ForwardCurve E)) (hne : S.Nonempty) : ForwardCurve E := by
  classical
  exact {
  lifetime := ⨆ c : S, c.val.lifetime
  positive_lifetime := by
    obtain ⟨c, hc⟩ := hne
    exact c.positive_lifetime.trans_le (le_iSup (fun d : S => d.val.lifetime) ⟨c, hc⟩)
  curve t := if hex : ∃ c ∈ S, c.InDomain t then (Classical.choose hex).curve t else 0 }

omit [NormedSpace ℝ E] in
theorem chainUpper_curve_eq {S : Set (ForwardCurve E)} (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) {c : ForwardCurve E} (hc : c ∈ S)
    {t : ℝ} (ht : c.InDomain t) : (chainUpper S hne).curve t = c.curve t := by
  have hex : ∃ d ∈ S, d.InDomain t := ⟨c, hc, ht⟩
  simp only [chainUpper, dif_pos hex]
  have hd := Classical.choose_spec hex
  rcases hchain.total hc hd.1 with hcd | hdc
  · exact hcd.2 t ht
  · exact (hdc.2 t hd.2).symm

omit [NormedSpace ℝ E] in
theorem chainUpper_extends {S : Set (ForwardCurve E)} (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S) {c : ForwardCurve E} (hc : c ∈ S) :
    (chainUpper S hne).Extends c := by
  refine ⟨le_iSup (fun d : S => d.val.lifetime) ⟨c, hc⟩, ?_⟩
  intro t ht
  exact chainUpper_curve_eq hne hchain hc ht

omit [NormedSpace ℝ E] in
theorem chainUpper_domain_witness {S : Set (ForwardCurve E)} (hne : S.Nonempty)
    {t : ℝ} (ht : (chainUpper S hne).InDomain t) :
    ∃ c ∈ S, c.InDomain t := by
  obtain ⟨c, hc⟩ := lt_iSup_iff.mp ht.2
  exact ⟨c.val, c.property, ht.1, hc⟩

/-- A chain union solves the same ODE because it agrees locally with one
member of the chain at every time before its supremal lifetime. -/
theorem chainUpper_solves {F : E → E} {S : Set (ForwardCurve E)}
    (hne : S.Nonempty) (hchain : IsChain (· ≤ ·) S)
    (hsolve : ∀ c ∈ S, SolvesODE F c) : SolvesODE F (chainUpper S hne) := by
  intro t ht
  obtain ⟨c, hc, hct⟩ := chainUpper_domain_witness hne ht
  have hbound : ∀ᶠ s in 𝓝 t, ENNReal.ofReal s < c.lifetime :=
    (ENNReal.continuous_ofReal.tendsto t).eventually (gt_mem_nhds hct.2)
  have he : (chainUpper S hne).curve =ᶠ[𝓝[Ici 0] t] c.curve := by
    filter_upwards [hbound.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with s hs hs0
    exact chainUpper_curve_eq hne hchain hc ⟨hs0, hs⟩
  have hvalue := chainUpper_curve_eq hne hchain hc hct
  have hd := (hsolve c hc t hct).congr_of_eventuallyEq he hvalue
  simpa only [hvalue] using hd

/-- Every classical forward solution has a maximal extension. In particular,
estimates quantified over all maximal solutions apply to every given solution
segment after taking such an extension. -/
theorem exists_maximal_extension {F : E → E} {c : ForwardCurve E}
    (hc : SolvesODE F c) :
    ∃ d : ForwardCurve E, d.Extends c ∧ MaximalSolution F d := by
  have hchain : ∀ S ⊆ {d : ForwardCurve E | SolvesODE F d},
      IsChain (· ≤ ·) S → ∀ y ∈ S,
      ∃ ub ∈ {d : ForwardCurve E | SolvesODE F d}, ∀ z ∈ S, z ≤ ub := by
    intro S hS hSchain y hy
    have hne : S.Nonempty := ⟨y, hy⟩
    refine ⟨chainUpper S hne, chainUpper_solves hne hSchain (fun d hd => hS hd), ?_⟩
    intro z hz
    exact chainUpper_extends hne hSchain hz
  obtain ⟨d, hcd, hdsol, hdmax⟩ :=
    zorn_le_nonempty₀ {d : ForwardCurve E | SolvesODE F d} hchain c hc
  refine ⟨d, hcd, hdsol, ?_⟩
  intro e hesol hed
  have hde : e ≤ d := hdmax hesol hed
  exact le_antisymm hde.1 hed.1

/-- Stability over maximal solutions controls every solution segment. The proof
uses an actual maximal extension and does not assume uniqueness. -/
theorem stable_all_solutions_of_stable_maximal {F : E → E} {p : E}
    (hs : StrongStable (MaximalSolutions F) p) :
    StrongStable {c : ForwardCurve E | SolvesODE F c} p := by
  intro ε hε
  obtain ⟨δ, hδ, hδspec⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro c hc hinit t ht
  obtain ⟨d, hdc, hdmax⟩ := exists_maximal_extension hc
  have hdinit : dist (d.curve 0) p < δ := by
    simpa only [hdc.2 0 c.zero_inDomain] using hinit
  have hdt : d.InDomain t := ⟨ht.1, ht.2.trans_le hdc.1⟩
  simpa only [hdc.2 t ht] using hδspec d hdmax hdinit t hdt

/-- Taking the union of a chain also preserves any specified state-space
domain: each state is the state of one chain member. -/
theorem chainUpper_solves_on {F : E → E} {U : Set E}
    {S : Set (ForwardCurve E)} (hne : S.Nonempty)
    (hchain : IsChain (· ≤ ·) S)
    (hsolve : ∀ c ∈ S, SolvesODEOn F U c) :
    SolvesODEOn F U (chainUpper S hne) := by
  refine ⟨chainUpper_solves hne hchain (fun c hc => (hsolve c hc).1), ?_⟩
  intro t ht
  obtain ⟨c, hc, hct⟩ := chainUpper_domain_witness hne ht
  rw [chainUpper_curve_eq hne hchain hc hct]
  exact (hsolve c hc).2 t hct

/-- Every solution staying in `U` has an extension maximal among solutions
staying in `U`. Neither openness of `U` nor uniqueness is needed. -/
theorem exists_maximal_extension_on {F : E → E} {U : Set E}
    {c : ForwardCurve E} (hc : SolvesODEOn F U c) :
    ∃ d : ForwardCurve E, d.Extends c ∧ MaximalSolutionOn F U d := by
  have hchain : ∀ S ⊆ {d : ForwardCurve E | SolvesODEOn F U d},
      IsChain (· ≤ ·) S → ∀ y ∈ S,
      ∃ ub ∈ {d : ForwardCurve E | SolvesODEOn F U d}, ∀ z ∈ S, z ≤ ub := by
    intro S hS hSchain y hy
    have hne : S.Nonempty := ⟨y, hy⟩
    refine ⟨chainUpper S hne,
      chainUpper_solves_on hne hSchain (fun d hd => hS hd), ?_⟩
    intro z hz
    exact chainUpper_extends hne hSchain hz
  obtain ⟨d, hcd, hdsol, hdmax⟩ :=
    zorn_le_nonempty₀ {d : ForwardCurve E | SolvesODEOn F U d} hchain c hc
  refine ⟨d, hcd, hdsol, ?_⟩
  intro e hesol hed
  have hde : e ≤ d := hdmax hesol hed
  exact le_antisymm hde.1 hed.1

/-- Stability of all maximal solutions in a domain controls every finite
solution segment staying in that domain. -/
theorem stable_all_solutions_of_stable_maximal_on {F : E → E} {U : Set E} {p : E}
    (hs : StrongStable (MaximalSolutionsOn F U) p) :
    StrongStable {c : ForwardCurve E | SolvesODEOn F U c} p := by
  intro ε hε
  obtain ⟨δ, hδ, hδspec⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro c hc hinit t ht
  obtain ⟨d, hdc, hdmax⟩ := exists_maximal_extension_on hc
  have hdinit : dist (d.curve 0) p < δ := by
    simpa only [hdc.2 0 c.zero_inDomain] using hinit
  have hdt : d.InDomain t := ⟨ht.1, ht.2.trans_le hdc.1⟩
  simpa only [hdc.2 t ht] using hδspec d hdmax hdinit t hdt

end CBFIndependence.MaximalExtension
