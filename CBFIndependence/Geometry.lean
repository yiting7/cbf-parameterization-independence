import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Geometry of regular scalar defining functions

The normal is represented by a continuous linear functional, avoiding a choice of
inner product. The results apply to real Banach spaces; finite dimensional state
spaces are a special case. No optimization or trajectory assumptions occur here.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace CBFIndependence.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The safe set represented by a scalar defining function. -/
def superlevel (h : E → ℝ) : Set E := {x | 0 ≤ h x}

/-- Equality of safe sets is equality of nonnegative superlevel sets. -/
def SameSafeSet (h₁ h₂ : E → ℝ) : Prop := superlevel h₁ = superlevel h₂

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem sameSafeSet_iff {h₁ h₂ : E → ℝ} :
    SameSafeSet h₁ h₂ ↔ ∀ x, (0 ≤ h₁ x ↔ 0 ≤ h₂ x) := by
  simp only [SameSafeSet, superlevel, Set.ext_iff, Set.mem_setOf_eq]

omit [NormedSpace ℝ E] in
/-- Boundary vanishing is local: continuity only at the boundary point is needed. -/
theorem zero_of_mem_frontier_of_continuousAt {h : E → ℝ} {p : E}
    (hc : ContinuousAt h p) (hp : p ∈ frontier (superlevel h)) : h p = 0 := by
  have hge : 0 ≤ h p := by
    by_contra! hn
    have hf := mem_closure_iff_frequently.mp hp.1
    apply hf
    filter_upwards [hc.eventually (gt_mem_nhds hn)] with x hx
    exact not_le.mpr hx
  have hle : h p ≤ 0 := by
    by_contra! hn
    apply hp.2
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hc.eventually (lt_mem_nhds hn)] with x hx
    exact hx.le
  exact le_antisymm hle hge

omit [NormedSpace ℝ E] in
/-- Every boundary point of a continuous defining function has value zero. -/
theorem zero_of_mem_frontier {h : E → ℝ} (hc : Continuous h) {p : E}
    (hp : p ∈ frontier (superlevel h)) : h p = 0 := by
  exact zero_of_mem_frontier_of_continuousAt hc.continuousAt hp

omit [NormedSpace ℝ E] in
/-- Boundary membership depends only on the germ of a set at the point. -/
theorem mem_frontier_iff_of_eventuallyEq {s t : Set E} {p : E}
    (hs : s =ᶠ[𝓝 p] t) : p ∈ frontier s ↔ p ∈ frontier t := by
  have hcompl : sᶜ =ᶠ[𝓝 p] tᶜ := by
    filter_upwards [hs] with x hx
    exact congrArg Not hx
  simp only [frontier, mem_diff, closure_eq_compl_interior_compl, mem_compl_iff]
  exact and_congr (not_congr hcompl.mem_interior_iff) (not_congr hs.mem_interior_iff)

omit [NormedSpace ℝ E] in
/-- Locally equal sets have locally equal frontiers. -/
theorem frontiers_eventuallyEq {s t : Set E} {p : E}
    (hs : s =ᶠ[𝓝 p] t) : frontier s =ᶠ[𝓝 p] frontier t := by
  apply Filter.eventuallyEq_set.mpr
  filter_upwards [hs.eventually_nhds] with x hx
  exact mem_frontier_iff_of_eventuallyEq hx

/-- Directional differentiation along an affine line. -/
theorem hasDerivAt_on_line {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hd : HasFDerivAt h L p) (v : E) :
    HasDerivAt (fun t : ℝ => h (p + t • v)) (L v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hd' : HasFDerivAt h L (p + (0 : ℝ) • v) := by simpa using hd
  exact hd'.comp_hasDerivAt 0 hl

/-- Equal superlevel sets force a nonnegative second normal derivative in every
strictly inward direction for the first defining function. -/
theorem normal_nonneg_of_inward_of_eventuallyEq {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hz₁ : h₁ p = 0) (hz₂ : h₂ p = 0)
    (hs : superlevel h₁ =ᶠ[𝓝 p] superlevel h₂)
    {v : E} (hv : 0 < L₁ v) : 0 ≤ L₂ v := by
  have ht₁ := (hasDerivAt_on_line hd₁ v).tendsto_slope_zero_right
  have ht₂ := (hasDerivAt_on_line hd₂ v).tendsto_slope_zero_right
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t⁻¹ * h₁ (p + t • v) := by
    simpa [hz₁] using ht₁.eventually (lt_mem_nhds hv)
  have hline : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsame := hline.eventually hs.mem_iff
  apply ge_of_tendsto ht₂
  filter_upwards [he, self_mem_nhdsWithin, hsame] with t ht htpos hsame_t
  have htpos' : 0 < t := htpos
  have hh₁ : 0 ≤ h₁ (p + t • v) := by
    have : 0 < h₁ (p + t • v) :=
      (mul_pos_iff_of_pos_left (inv_pos.mpr htpos')).mp ht
    exact this.le
  have hh₂ := hsame_t.mp hh₁
  simpa [hz₂] using mul_nonneg (inv_nonneg.mpr htpos'.le) hh₂

theorem normal_nonneg_of_inward {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hz₁ : h₁ p = 0) (hz₂ : h₂ p = 0) (hs : SameSafeSet h₁ h₂)
    {v : E} (hv : 0 < L₁ v) : 0 ≤ L₂ v := by
  apply normal_nonneg_of_inward_of_eventuallyEq hd₁ hd₂ hz₁ hz₂ _ hv
  rw [show superlevel h₁ = superlevel h₂ from hs]

/-- A nonzero real covector admits a normalized transverse vector. -/
theorem exists_normal_unit {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∃ v : E, L v = 1 := by
  have hex : ∃ v : E, L v ≠ 0 := by
    by_contra! h
    apply hL
    ext v
    exact h v
  obtain ⟨v, hv⟩ := hex
  refine ⟨(L v)⁻¹ • v, ?_⟩
  simp [hv]

/-- Linear algebra behind the orientation of a regular level set. -/
theorem positive_multiple_of_halfspace {L₁ L₂ : E →L[ℝ] ℝ}
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0)
    (hpos : ∀ v, 0 < L₁ v → 0 ≤ L₂ v) :
    ∃ c : ℝ, 0 < c ∧ L₂ = c • L₁ := by
  obtain ⟨w, hw⟩ := exists_normal_unit hL₁
  have hk : ∀ v : E, L₁ v = 0 → L₂ v = 0 := by
    intro v hv
    by_contra hv₂
    have hp := hpos (w - ((L₂ w + 1) / L₂ v) • v) (by simp [hv, hw])
    have he : L₂ (w - ((L₂ w + 1) / L₂ v) • v) = -1 := by
      simp only [map_sub, map_smul, smul_eq_mul]
      field_simp
      ring
    rw [he] at hp
    linarith
  have hscalar : L₂ = (L₂ w) • L₁ := by
    ext v
    have ht := hk (v - (L₁ v) • w) (by simp [hw])
    simp only [map_sub, map_smul, smul_eq_mul] at ht
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    nlinarith
  refine ⟨L₂ w, ?_, hscalar⟩
  have hn : 0 ≤ L₂ w := hpos w (by rw [hw]; norm_num)
  have hne : L₂ w ≠ 0 := by
    intro he
    apply hL₂
    simpa [he] using hscalar
  exact lt_of_le_of_ne hn (Ne.symm hne)

/-- Equal superlevel sets have positively proportional nonzero boundary normals.
Only pointwise differentiability is required for this conclusion. -/
theorem normals_positive_multiple {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hz₁ : h₁ p = 0) (hz₂ : h₂ p = 0) (hs : SameSafeSet h₁ h₂)
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ L₂ = c • L₁ :=
  positive_multiple_of_halfspace hL₁ hL₂
    (fun _ hv => normal_nonneg_of_inward hd₁ hd₂ hz₁ hz₂ hs hv)

/-- The positive normal relation only needs local equality of safe sets. -/
theorem normals_positive_multiple_of_eventuallyEq {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hz₁ : h₁ p = 0) (hz₂ : h₂ p = 0)
    (hs : superlevel h₁ =ᶠ[𝓝 p] superlevel h₂)
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ L₂ = c • L₁ :=
  positive_multiple_of_halfspace hL₁ hL₂
    (fun _ hv => normal_nonneg_of_inward_of_eventuallyEq hd₁ hd₂ hz₁ hz₂ hs hv)

/-- Positively proportional normals define the same tangent hyperplane. -/
theorem normal_kernels_eq_of_positive_multiple {L₁ L₂ : E →L[ℝ] ℝ}
    {c : ℝ} (hc : 0 < c) (he : L₂ = c • L₁) :
    LinearMap.ker L₁ = LinearMap.ker L₂ := by
  ext v
  simp [he, hc.ne', LinearMap.mem_ker]

theorem normals_positive_multiple_at_boundary_of_eventuallyEq {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hs : superlevel h₁ =ᶠ[𝓝 p] superlevel h₂) (hp : p ∈ frontier (superlevel h₁))
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ L₂ = c • L₁ := by
  exact normals_positive_multiple_of_eventuallyEq hd₁ hd₂
    (zero_of_mem_frontier_of_continuousAt hd₁.continuousAt hp)
    (zero_of_mem_frontier_of_continuousAt hd₂.continuousAt
      ((mem_frontier_iff_of_eventuallyEq hs).mp hp))
    hs hL₁ hL₂

theorem normals_positive_multiple_at_boundary {h₁ h₂ : E → ℝ}
    {L₁ L₂ : E →L[ℝ] ℝ} {p : E}
    (hc₁ : Continuous h₁) (hc₂ : Continuous h₂)
    (hd₁ : HasFDerivAt h₁ L₁ p) (hd₂ : HasFDerivAt h₂ L₂ p)
    (hs : SameSafeSet h₁ h₂) (hp : p ∈ frontier (superlevel h₁))
    (hL₁ : L₁ ≠ 0) (hL₂ : L₂ ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ L₂ = c • L₁ := by
  have hp₂ : p ∈ frontier (superlevel h₂) := by
    rw [← hs]
    exact hp
  exact normals_positive_multiple hd₁ hd₂
    (zero_of_mem_frontier hc₁ hp) (zero_of_mem_frontier hc₂ hp₂) hs hL₁ hL₂

/-- Regular zero-level points are boundary points, even with just a derivative
at the point. This supplies the converse to `zero_of_mem_frontier`. -/
theorem mem_frontier_of_regular_zero {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hd : HasFDerivAt h L p) (hz : h p = 0) (hL : L ≠ 0) :
    p ∈ frontier (superlevel h) := by
  obtain ⟨v, hv⟩ := exists_normal_unit hL
  have ht := (hasDerivAt_on_line hd (-v)).tendsto_slope_zero_right
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t⁻¹ * h (p + t • (-v)) < 0 := by
    have hn : L (-v) < 0 := by simp [hv]
    simpa [hz] using ht.eventually (gt_mem_nhds hn)
  have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, p + t • (-v) ∈ (superlevel h)ᶜ := by
    filter_upwards [he, self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    have hh : h (p + t • (-v)) < 0 := by
      by_contra hh
      have hm := mul_nonneg (inv_nonneg.mpr htpos'.le) (le_of_not_gt hh)
      linarith
    exact not_le.mpr hh
  have hconv : Tendsto (fun t : ℝ => p + t • (-v)) (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • (-v)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure (by simp [superlevel, hz]), mem_closure_of_tendsto hconv hn⟩

/-- The active CBF identity gives the scalar normal ODE along every
differentiable solution, without a uniqueness assumption. -/
theorem normal_derivative_along_solution {h : E → ℝ} {F : E → E}
    {α : ℝ → ℝ} {γ : ℝ → E} {t : ℝ} {L : E →L[ℝ] ℝ}
    (hh : HasFDerivAt h L (γ t)) (hγ : HasDerivAt γ (F (γ t)) t)
    (hactive : L (F (γ t)) = -α (h (γ t))) :
    HasDerivAt (fun s => h (γ s)) (-α (h (γ t))) t := by
  simpa only [hactive] using hh.comp_hasDerivAt t hγ

/-- A regular real-valued derivative is surjective. -/
theorem normal_range_eq_top {L : E →L[ℝ] ℝ} (hL : L ≠ 0) :
    LinearMap.range L = ⊤ := by
  obtain ⟨v, hv⟩ := exists_normal_unit hL
  apply LinearMap.range_eq_top.mpr
  intro r
  exact ⟨r • v, by simp [hv]⟩

section LocalCoordinates

variable [CompleteSpace E]

/-- A regular C¹ defining function supplies actual local normal coordinates.
The first coordinate is the defining function itself and the remaining
coordinates belong to the kernel of its derivative at the base point. -/
def normalCoordinates {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0) :
    OpenPartialHomeomorph E (ℝ × LinearMap.ker L) :=
  (hc.hasStrictFDerivAt' hd (by norm_num)).implicitToOpenPartialHomeomorph
    h L (normal_range_eq_top hL)

@[simp] theorem normalCoordinates_fst {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0) (x : E) :
    (normalCoordinates hc hd hL x).1 = h x := rfl

@[simp] theorem normalCoordinates_self {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0) :
    normalCoordinates hc hd hL p = (h p, 0) := by
  exact HasStrictFDerivAt.implicitToOpenPartialHomeomorph_self _ _

theorem mem_normalCoordinates_source {h : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0) :
    p ∈ (normalCoordinates hc hd hL).source := by
  exact HasStrictFDerivAt.mem_implicitToOpenPartialHomeomorph_source _ _

theorem normalCoordinates_mem_halfspace_iff {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0) (x : E) :
    0 ≤ (normalCoordinates hc hd hL x).1 ↔ x ∈ superlevel h := Iff.rfl

/-- On the actual chart source, the safe-set boundary is exactly the zero
normal-coordinate hyperplane. No extra regularity assumption at nearby points
is hidden in this statement. -/
theorem normalCoordinates_boundary_iff {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p x : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0)
    (hx : x ∈ (normalCoordinates hc hd hL).source) :
    x ∈ frontier (superlevel h) ↔ h x = 0 := by
  let e := normalCoordinates hc hd hL
  have himage : e.IsImage (superlevel h) (Ici (0 : ℝ) ×ˢ (univ : Set (LinearMap.ker L))) := by
    intro y hy
    simp [e, superlevel]
  have hh := himage.frontier hx
  simpa [e] using hh.symm

theorem normalCoordinates_inverse_first {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0)
    {y : ℝ × LinearMap.ker L} (hy : y ∈ (normalCoordinates hc hd hL).target) :
    h ((normalCoordinates hc hd hL).symm y) = y.1 := by
  exact congrArg Prod.fst ((normalCoordinates hc hd hL).right_inv hy)

theorem normalCoordinates_inverse_zero {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0)
    (hz : h p = 0) : (normalCoordinates hc hd hL).symm 0 = p := by
  have hi := (normalCoordinates hc hd hL).left_inv (mem_normalCoordinates_source hc hd hL)
  simpa [normalCoordinates_self, hz] using hi

/-- Local normal coordinates preserve convergence to the equilibrium. The
eventual-source condition is explicit: this theorem makes no forward
completeness or trajectory confinement claim. -/
theorem tendsto_normalCoordinates_iff {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0)
    (hz : h p = 0) {ι : Type*} {l : Filter ι} {γ : ι → E}
    (hsource : ∀ᶠ t in l, γ t ∈ (normalCoordinates hc hd hL).source) :
    Tendsto (fun t => normalCoordinates hc hd hL (γ t)) l (𝓝 0) ↔
      Tendsto γ l (𝓝 p) := by
  let e := normalCoordinates hc hd hL
  have hp : p ∈ e.source := mem_normalCoordinates_source hc hd hL
  have hzero : e p = 0 := by simp [e, hz]
  constructor
  · intro ht
    have hinv : ContinuousAt e.symm 0 := by
      rw [← hzero]
      exact e.continuousAt_symm (e.map_source hp)
    have hcomp : Tendsto (fun t => e.symm (e (γ t))) l (𝓝 p) := by
      have hh := hinv.tendsto.comp ht
      simpa [e, normalCoordinates_inverse_zero hc hd hL hz] using hh
    exact (tendsto_congr' (hsource.mono fun t hx => e.left_inv hx)).mp hcomp
  · intro ht
    simpa [hzero] using (e.continuousAt hp).tendsto.comp ht

theorem boundary_parametrization_hasFDerivAt {h : E → ℝ}
    {L : E →L[ℝ] ℝ} {p : E}
    (hc : ContDiffAt ℝ 1 h p) (hd : HasFDerivAt h L p) (hL : L ≠ 0)
    (hz : h p = 0) :
    HasFDerivAt (fun z : LinearMap.ker L =>
      (normalCoordinates hc hd hL).symm (0, z)) (LinearMap.ker L).subtypeL 0 := by
  have hf := hc.hasStrictFDerivAt' hd (by norm_num : (1 : WithTop ℕ∞) ≤ 1)
  simpa [HasStrictFDerivAt.implicitFunction, normalCoordinates, hz] using
    (hf.to_implicitFunction (normal_range_eq_top hL)).hasFDerivAt

end LocalCoordinates

end CBFIndependence.Geometry
