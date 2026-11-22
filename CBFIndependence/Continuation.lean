import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Order.OrderClosed

/-!
# Finite endpoint limits for continuous ODEs

A solution remaining in a compact set has a limit at a finite right endpoint.
The gluing theorem extends it through that point using any local solution
starting there. `CBFIndependence.CompactContinuation` supplies one by Peano existence.
-/

noncomputable section

open Set Filter
open scoped Topology NNReal

namespace CBFIndependence.Continuation

section Uniform

variable {X Y : Type*} [UniformSpace X] [UniformSpace Y]

/-- Uniform continuity on a filter-large set maps a Cauchy filter to a Cauchy
filter. This avoids requiring global uniform continuity of a trajectory. -/
theorem cauchy_map_of_uniformContinuousOn {f : X → Y} {s : Set X} {l : Filter X}
    (hf : UniformContinuousOn f s) (hl : Cauchy l) (hs : s ∈ l) :
    Cauchy (Filter.map f l) := by
  rw [cauchy_map_iff]
  refine ⟨hl.1, hf.mono_left ?_⟩
  exact le_inf hl.2 (Filter.le_principal_iff.mpr (Filter.prod_mem_prod hs hs))

end Uniform

section Endpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A uniformly continuous curve confined to a compact set has a limit at a
finite right endpoint. No completeness assumption on the ambient space is
needed because the compact range is complete. -/
theorem exists_endpoint_of_uniformContinuousOn {γ : ℝ → E} {T : ℝ} {K : Set E}
    (hT : 0 < T) (hK : IsCompact K)
    (hγ : UniformContinuousOn γ (Ico 0 T))
    (hinside : ∀ t ∈ Ico 0 T, γ t ∈ K) :
    ∃ x ∈ K, Tendsto γ (𝓝[<] T) (𝓝 x) := by
  have hdomain : Ico 0 T ∈ 𝓝[<] T := Ico_mem_nhdsLT hT
  have hc : Cauchy (𝓝[<] T) := cauchy_nhds.mono nhdsWithin_le_nhds
  have hcγ := cauchy_map_of_uniformContinuousOn hγ hc hdomain
  have hmap : Filter.map γ (𝓝[<] T) ≤ 𝓟 K := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ t in 𝓝[<] T, γ t ∈ K
    exact Filter.mem_of_superset hdomain hinside
  exact hK.isComplete _ hcγ hmap

/-- A continuously driven classical solution confined to a compact set is
uniformly Lipschitz in time on its finite lifetime. -/
theorem exists_lipschitzOnWith_of_compact_range {F : E → E} {γ : ℝ → E}
    {T : ℝ} {K : Set E}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hγ : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (F (γ t)) (Ici 0) t)
    (hinside : ∀ t ∈ Ico 0 T, γ t ∈ K) :
    ∃ C : ℝ≥0, LipschitzOnWith C γ (Ico 0 T) := by
  obtain ⟨C, hC, hbound⟩ :=
    (hK.image_of_continuousOn hF).isBounded.exists_pos_norm_le
  refine ⟨⟨C, hC.le⟩, ?_⟩
  apply (convex_Ico (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro t ht
    exact (hγ t ht).mono Ico_subset_Ici_self
  · intro t ht
    exact hbound (F (γ t)) ⟨γ t, hinside t ht, rfl⟩

/-- The finite-endpoint step in the continuation theorem for a continuous
autonomous vector field. Every trajectory staying in a compact set converges
to a point of that set as its finite lifetime is approached. -/
theorem exists_endpoint_of_continuous_field {F : E → E} {γ : ℝ → E}
    {T : ℝ} {K : Set E}
    (hT : 0 < T) (hK : IsCompact K) (hF : ContinuousOn F K)
    (hγ : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (F (γ t)) (Ici 0) t)
    (hinside : ∀ t ∈ Ico 0 T, γ t ∈ K) :
    ∃ x ∈ K, Tendsto γ (𝓝[<] T) (𝓝 x) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_of_compact_range hK hF hγ hinside
  exact exists_endpoint_of_uniformContinuousOn hT hK hC.uniformContinuousOn hinside

/-- If the endpoint value has been filled in by the limiting state, continuity
of the vector field extends the ODE derivative to that endpoint from the left. -/
theorem hasDerivWithinAt_endpoint {F : E → E} {γ : ℝ → E} {T : ℝ}
    (hT : 0 < T) (hF : ContinuousAt F (γ T))
    (hγ : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (F (γ t)) (Ici 0) t)
    (hlim : Tendsto γ (𝓝[<] T) (𝓝 (γ T))) :
    HasDerivWithinAt γ (F (γ T)) (Iic T) T := by
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt γ (F (γ t)) t := by
    intro t ht
    exact (hγ t ⟨ht.1.le, ht.2⟩).hasDerivAt (Ici_mem_nhds ht.1)
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (hlim.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self))
    (Ioo_mem_nhdsLT hT)
  apply (hF.tendsto.comp hlim).congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  exact (hd t ht).deriv.symm

/-- The actual concatenation used to continue a trajectory past `T`. -/
def glueAt (γ η : ℝ → E) (T : ℝ) (t : ℝ) : E := if t < T then γ t else η t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glueAt_eq_left {γ η : ℝ → E} {T t : ℝ} (ht : t < T) :
    glueAt γ η T =ᶠ[𝓝 t] γ := by
  filter_upwards [gt_mem_nhds ht] with s hs
  simp [glueAt, hs]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem glueAt_eq_right {γ η : ℝ → E} {T t : ℝ} (ht : T < t) :
    glueAt γ η T =ᶠ[𝓝 t] η := by
  filter_upwards [lt_mem_nhds ht] with s hs
  simp [glueAt, not_lt.mpr hs.le]

/-- Glue a left solution to a right solution starting at its endpoint limit. -/
theorem glueAt_solves {F : E → E} {γ η : ℝ → E} {T U : ℝ}
    (hT : 0 < T) (hTU : T < U) (hF : ContinuousAt F (η T))
    (hγ : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (F (γ t)) (Ici 0) t)
    (hη : ∀ t ∈ Ico T U, HasDerivWithinAt η (F (η t)) (Ici T) t)
    (hlim : Tendsto γ (𝓝[<] T) (𝓝 (η T))) :
    ∀ t ∈ Ico 0 U,
      HasDerivWithinAt (glueAt γ η T) (F (glueAt γ η T t)) (Ici 0) t := by
  have hleft : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (glueAt γ η T) (F (glueAt γ η T t)) (Ici 0) t := by
    intro t ht
    have he := glueAt_eq_left (γ := γ) (η := η) ht.2
    have hh := (hγ t ht).congr_of_eventuallyEq (he.filter_mono nhdsWithin_le_nhds)
      (he.eq_of_nhds)
    simpa [glueAt, ht.2] using hh
  intro t ht
  rcases lt_trichotomy t T with hlt | heq | hgt
  · exact hleft t ⟨ht.1, hlt⟩
  · subst t
    have hglim : Tendsto (glueAt γ η T) (𝓝[<] T) (𝓝 (glueAt γ η T T)) := by
      have he : glueAt γ η T =ᶠ[𝓝[<] T] γ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : s < T := hs
        simp [glueAt, hs']
      simpa [glueAt] using (tendsto_congr' he).mpr hlim
    have hl : HasDerivWithinAt (glueAt γ η T) (F (glueAt γ η T T)) (Iic T) T :=
      hasDerivWithinAt_endpoint hT (by simpa [glueAt] using hF) hleft hglim
    have hr : HasDerivWithinAt (glueAt γ η T) (F (glueAt γ η T T)) (Ici T) T := by
      have hh := (hη T ⟨le_rfl, hTU⟩).congr_of_mem (f₁ := glueAt γ η T)
        (fun s hs => by
          have hs' : T ≤ s := hs
          simp [glueAt, not_lt.mpr hs']) (by simp : T ∈ Ici T)
      simpa [glueAt] using hh
    have hall : HasDerivAt (glueAt γ η T) (F (glueAt γ η T T)) T := by
      simpa using hl.union hr
    exact hall.hasDerivWithinAt
  · have he := glueAt_eq_right (γ := γ) (η := η) hgt
    have hh := (hη t ⟨hgt.le, ht.2⟩).hasDerivAt (Ici_mem_nhds hgt)
    have hh' := hh.congr_of_eventuallyEq he
    simpa [glueAt, not_lt.mpr hgt.le] using hh'.hasDerivWithinAt (s := Ici 0)

end Endpoint

end CBFIndependence.Continuation
