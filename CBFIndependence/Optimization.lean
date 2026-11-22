import CBFIndependence.Statement
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

open Set Filter Topology

namespace CBFIndependence.Optimization

variable {X E : Type*}

theorem minimizer_unique [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} {K : Set E} {u v : E}
    (hf : StrictConvexOn ℝ K f) (hu : Minimizes f K u) (hv : Minimizes f K v) :
    u = v := by
  exact hf.eq_of_isMinOn hu.2 hv.2 hu.1 hv.1

theorem existsUnique_minimizer_of_compact
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hcont : ContinuousOn f K) (hstrict : StrictConvexOn ℝ K f) :
    ∃! z, Minimizes f K z := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨z, ⟨hz, hmin⟩, ?_⟩
  intro y hy
  exact minimizer_unique hstrict hy ⟨hz, hmin⟩

/-- Coercivity is expressed by convergence to `atTop` along the cocompact filter. -/
theorem existsUnique_minimizer_of_coercive
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {f : E → ℝ} {K : Set E}
    (hK : IsClosed K) (hne : K.Nonempty)
    (hcont : ContinuousOn f K) (hstrict : StrictConvexOn ℝ K f)
    (hcoercive : Tendsto f (cocompact E) atTop) :
    ∃! z, Minimizes f K z := by
  obtain ⟨w, hw⟩ := hne
  have haway : ∀ᶠ z in cocompact E ⊓ 𝓟 K, f w ≤ f z :=
    (hcoercive.eventually (eventually_ge_atTop (f w))).filter_mono inf_le_left
  obtain ⟨z, hz, hmin⟩ := hcont.exists_isMinOn' hK hw haway
  refine ⟨z, ⟨hz, hmin⟩, ?_⟩
  intro y hy
  exact minimizer_unique hstrict hy ⟨hz, hmin⟩

theorem strictlyFeasible_eventually [TopologicalSpace X]
    {q : ℕ} {c : Fin q → X → E → ℝ} {p : X} {z : E}
    (hc : ∀ j, ContinuousAt (fun x => c j x z) p)
    (hz : StrictlyFeasible c p z) :
    ∀ᶠ x in 𝓝 p, StrictlyFeasible c x z := by
  unfold StrictlyFeasible
  apply eventually_all.2
  intro j
  exact (hc j).eventually (gt_mem_nhds (hz j))

theorem feasible_isClosed [TopologicalSpace E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {x : X}
    (hc : ∀ j, Continuous (c j x)) : IsClosed (Feasible c x) := by
  have heq : Feasible c x = ⋂ j, {z | c j x z ≤ 0} := by
    ext z
    simp [Feasible]
  rw [heq]
  exact isClosed_iInter fun j => isClosed_le (hc j) continuous_const

theorem feasible_convex [AddCommMonoid E] [Module ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {x : X}
    (hc : ∀ j, ConvexOn ℝ univ (c j x)) : Convex ℝ (Feasible c x) := by
  intro u hu v hv a b ha hb hab j
  have hj := (hc j).2 (mem_univ u) (mem_univ v) ha hb hab
  calc
    c j x (a • u + b • v) ≤ a • c j x u + b • c j x v := hj
    _ ≤ 0 := by
      simpa only [smul_eq_mul] using
        add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hu j))
          (mul_nonpos_of_nonneg_of_nonpos hb (hv j))

theorem strictlyFeasible_combo [AddCommMonoid E] [Module ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {x : X} {u v : E} {t : ℝ}
    (hc : ∀ j, ConvexOn ℝ univ (c j x))
    (hu : u ∈ Feasible c x) (hv : StrictlyFeasible c x v)
    (ht : 0 < t) (ht1 : t ≤ 1) :
    StrictlyFeasible c x ((1 - t) • u + t • v) := by
  intro j
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hj := (hc j).2 (mem_univ u) (mem_univ v) ha ht.le (by ring)
  have hfirst := mul_nonpos_of_nonneg_of_nonpos ha (hu j)
  have hsecond := mul_neg_of_pos_of_neg ht (hv j)
  simp only [smul_eq_mul] at hj
  linarith

/-- Slater points approximate every feasible point while retaining strict feasibility. -/
theorem le_on_feasible_of_le_on_strictlyFeasible
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {x : X} {f : E → ℝ} {a : ℝ}
    (hc : ∀ j, ConvexOn ℝ univ (c j x)) (hf : Continuous f)
    (hslater : ∃ v, StrictlyFeasible c x v)
    (hbound : ∀ v, StrictlyFeasible c x v → a ≤ f v) :
    ∀ u ∈ Feasible c x, a ≤ f u := by
  obtain ⟨v, hv⟩ := hslater
  intro u hu
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have ht : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htone (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcurve : Tendsto (fun n => (1 - t n) • u + t n • v) atTop (𝓝 u) := by
    have h1 : Tendsto (fun n => (1 : ℝ) - t n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub ht :
        Tendsto (fun n => (1 : ℝ) - t n) atTop (𝓝 (1 - 0)))
    have h2 : Tendsto (fun n => (1 - t n) • u) atTop (𝓝 u) := by
      simpa using h1.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))
    have h3 : Tendsto (fun n => t n • v) atTop (𝓝 (0 : E)) := by
      simpa using ht.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
    simpa using h2.add h3
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hf.continuousAt.tendsto.comp hcurve)
  exact Eventually.of_forall fun n =>
    hbound _ (strictlyFeasible_combo hc hu hv (htpos n) (htone n))

/-- Local continuity of a parametric convex optimizer.  The compactness hypothesis
is a local range bound, not continuity of the optimizer.  It is separated out so
that coercive/sublevel estimates can be supplied independently. -/
theorem optimizer_continuousAt_of_eventually_compact
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ}
    {u : X → E} {p : X} {K : Set E}
    (hcompact : IsCompact K) (hrange : ∀ᶠ x in 𝓝 p, u x ∈ K)
    (hmin : ∀ᶠ x in 𝓝 p, Minimizes (f x) (Feasible c x) (u x))
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hcconv : ∀ j, ConvexOn ℝ univ (c j p))
    (hfstrict : StrictConvexOn ℝ (Feasible c p) (f p))
    (hslater : ∃ v, StrictlyFeasible c p v) : ContinuousAt u p := by
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt hrange
  intro z _hz hzcluster
  let L : Filter X := comap u (𝓝 z) ⊓ 𝓝 p
  haveI : NeBot L := neBot_inf_comap_iff_map'.2 hzcluster
  have hx : Tendsto (fun x : X => x) L (𝓝 p) := inf_le_right
  have hu : Tendsto u L (𝓝 z) := tendsto_comap.mono_left inf_le_left
  have hpair := hx.prodMk_nhds hu
  have hminL : ∀ᶠ x in L, Minimizes (f x) (Feasible c x) (u x) :=
    hmin.filter_mono inf_le_right
  have hzfeas : z ∈ Feasible c p := by
    intro j
    apply le_of_tendsto ((hc j).continuousAt.tendsto.comp hpair)
    exact hminL.mono fun x h => h.1 j
  have hcost : Tendsto (fun x => f x (u x)) L (𝓝 (f p z)) :=
    hf.continuousAt.tendsto.comp hpair
  have hzmin : ∀ v ∈ Feasible c p, f p z ≤ f p v := by
    apply le_on_feasible_of_le_on_strictlyFeasible hcconv
      (hf.comp (continuous_const.prodMk continuous_id)) hslater
    intro v hv
    have hvnear : ∀ᶠ x in 𝓝 p, StrictlyFeasible c x v :=
      strictlyFeasible_eventually
        (fun j => ((hc j).comp (continuous_id.prodMk continuous_const)).continuousAt) hv
    have htest : Tendsto (fun x => f x v) L (𝓝 (f p v)) :=
      hf.continuousAt.tendsto.comp (hx.prodMk_nhds tendsto_const_nhds)
    apply le_of_tendsto_of_tendsto hcost htest
    filter_upwards [hminL, hvnear.filter_mono inf_le_right] with x hm hs
    exact hm.2 v (fun j => (hs j).le)
  exact minimizer_unique hfstrict ⟨hzfeas, hzmin⟩ hmin.self_of_nhds


/-- Pointwise coercivity and joint continuity give a uniform local bound on
minimizers.  Convexity prevents a minimizer from crossing a high-cost sphere. -/
theorem optimizer_eventually_compact_of_coercive
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ}
    {u : X → E} {p : X}
    (hmin : ∀ᶠ x in 𝓝 p, Minimizes (f x) (Feasible c x) (u x))
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hconv : ∀ᶠ x in 𝓝 p, ConvexOn ℝ univ (f x))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hslater : ∃ w, StrictlyFeasible c p w)
    (hcoercive : Tendsto (f p) (cocompact E) atTop) :
    ∃ K : Set E, IsCompact K ∧ ∀ᶠ x in 𝓝 p, u x ∈ K := by
  obtain ⟨w, hw⟩ := hslater
  obtain ⟨C, hC, hCaway⟩ := mem_cocompact.mp
    (hcoercive.eventually (eventually_gt_atTop (f p w)))
  obtain ⟨r, hr, hCr⟩ := hC.isBounded.subset_closedBall_lt 0 w
  let R := r + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hsphere : ∀ z ∈ Metric.sphere w R, f p w < f p z := by
    intro z hz
    apply hCaway
    intro hzC
    have hzr : dist z w ≤ r := hCr hzC
    have hzR : dist z w = R := hz
    dsimp [R] at hzR
    linarith
  have hfw : Continuous (fun a : X × E => f a.1 w) :=
    hf.comp (continuous_fst.prodMk continuous_const)
  have hsphereNear : ∀ᶠ x in 𝓝 p, ∀ z ∈ Metric.sphere w R, f x w < f x z :=
    (isCompact_sphere w R).eventually_forall_of_forall_eventually
      (fun z hz => (isOpen_lt hfw hf).mem_nhds (hsphere z hz))
  have hwNear : ∀ᶠ x in 𝓝 p, StrictlyFeasible c x w :=
    strictlyFeasible_eventually
      (fun j => ((hc j).comp (continuous_id.prodMk continuous_const)).continuousAt) hw
  refine ⟨Metric.closedBall w R, isCompact_closedBall w R, ?_⟩
  filter_upwards [hmin, hconv, hsphereNear, hwNear] with x hm hcv hs hwx
  change dist (u x) w ≤ R
  by_contra hnot
  have hlarge : R < ‖u x - w‖ := by simpa only [dist_eq_norm] using lt_of_not_ge hnot
  have hnorm : 0 < ‖u x - w‖ := hR.trans hlarge
  let t : ℝ := R / ‖u x - w‖
  have ht : 0 < t := div_pos hR hnorm
  have ht1 : t ≤ 1 := (div_le_one hnorm).2 hlarge.le
  let z := (1 - t) • w + t • u x
  have hz : z ∈ Metric.sphere w R := by
    change dist z w = R
    rw [dist_eq_norm]
    have heq : z - w = t • (u x - w) := by
      dsimp [z]
      rw [sub_smul, one_smul, smul_sub]
      abel
    rw [heq, norm_smul, Real.norm_of_nonneg ht.le]
    exact div_mul_cancel₀ R hnorm.ne'
  have hminw : f x (u x) ≤ f x w := hm.2 w (fun j => (hwx j).le)
  have hcz := hcv.2 (mem_univ w) (mem_univ (u x))
    (sub_nonneg.mpr ht1) ht.le (show (1 - t) + t = 1 by ring)
  have hprod := mul_le_mul_of_nonneg_left hminw ht.le
  have hbad := hs z hz
  simp only [smul_eq_mul] at hcz
  dsimp [z] at hbad
  nlinarith

/-- A complete continuity theorem with Slater, convex constraints, a strictly
convex objective, and pointwise coercivity.  No compact feasible-set assumption
and no continuity assumption on the optimizer are used. -/
theorem optimizer_continuousAt_of_coercive
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ}
    {u : X → E} {p : X}
    (hmin : ∀ᶠ x in 𝓝 p, Minimizes (f x) (Feasible c x) (u x))
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hconv : ∀ᶠ x in 𝓝 p, ConvexOn ℝ univ (f x))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hcconv : ∀ j, ConvexOn ℝ univ (c j p))
    (hfstrict : StrictConvexOn ℝ univ (f p))
    (hslater : ∃ w, StrictlyFeasible c p w)
    (hcoercive : Tendsto (f p) (cocompact E) atTop) :
    ContinuousAt u p := by
  obtain ⟨K, hK, hKu⟩ := optimizer_eventually_compact_of_coercive
    hmin hf hconv hc hslater hcoercive
  exact optimizer_continuousAt_of_eventually_compact hK hKu hmin hf hc hcconv
    (hfstrict.subset (subset_univ _) (feasible_convex hcconv)) hslater


/-- A continuous strongly convex function on a proper real normed space is
coercive.  The proof uses the minimum on the unit ball and a quadratic lower
bound along rays; differentiability is not required. -/
theorem stronglyConvex_coercive
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {f : E → ℝ} {m : ℝ} (hm : 0 < m)
    (hf : Continuous f) (hstrong : StrongConvexOn univ m f) :
    Tendsto f (cocompact E) atTop := by
  obtain ⟨y, hy, hymin⟩ := (isCompact_closedBall (0 : E) 1).exists_isMinOn
    (show (Metric.closedBall (0 : E) 1).Nonempty from ⟨0, by simp⟩) hf.continuousOn
  let a := f 0
  let b := f y
  have hlower (x : E) (hx : 1 ≤ ‖x‖) :
      (m / 2 * ‖x‖ + (b - a - m / 2)) * ‖x‖ + a ≤ f x := by
    have hr : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
    let t : ℝ := 1 / ‖x‖
    have ht : 0 < t := one_div_pos.mpr hr
    have ht1 : t ≤ 1 := (div_le_one hr).2 hx
    have hz : t • x ∈ Metric.closedBall (0 : E) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]
      dsimp [t]
      rw [one_div_mul_cancel hr.ne']
    have hb : b ≤ f (t • x) := hymin hz
    have hs := hstrong.2 (mem_univ x) (mem_univ (0 : E))
      ht.le (sub_nonneg.mpr ht1) (show t + (1 - t) = 1 by ring)
    simp only [smul_zero, add_zero, sub_zero, smul_eq_mul] at hs
    have hmult := mul_le_mul_of_nonneg_left (hb.trans hs) hr.le
    have heq :
        ‖x‖ * (t * f x + (1 - t) * f 0 -
          t * (1 - t) * (m / 2 * ‖x‖ ^ 2)) =
          f x + (‖x‖ - 1) * f 0 - m / 2 * (‖x‖ ^ 2 - ‖x‖) := by
      dsimp [t]
      field_simp
    rw [heq] at hmult
    dsimp [a, b] at *
    nlinarith
  have hnorm : Tendsto (fun x : E => ‖x‖) (cocompact E) atTop :=
    tendsto_norm_cocompact_atTop
  have hlinear :
      Tendsto (fun x : E => m / 2 * ‖x‖ + (b - a - m / 2)) (cocompact E) atTop :=
    tendsto_atTop_add_const_right _ _ (hnorm.const_mul_atTop (by positivity))
  have hmodel :
      Tendsto (fun x : E => (m / 2 * ‖x‖ + (b - a - m / 2)) * ‖x‖ + a)
        (cocompact E) atTop :=
    tendsto_atTop_add_const_right _ _ (hlinear.atTop_mul_atTop₀ hnorm)
  apply tendsto_atTop_mono' _ _ hmodel
  exact (hnorm.eventually (eventually_ge_atTop 1)).mono fun x hx => hlower x hx

/-- Existence and uniqueness under the actual finite-dimensional strong-convexity
and Slater assumptions.  No compactness of the feasible set is imposed. -/
theorem existsUnique_minimizer_stronglyConvex
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {q : ℕ} {c : Fin q → E → ℝ} {f : E → ℝ} {m : ℝ}
    (hm : 0 < m) (hf : Continuous f) (hstrong : StrongConvexOn univ m f)
    (hc : ∀ j, Continuous (c j)) (hcconv : ∀ j, ConvexOn ℝ univ (c j))
    (hslater : ∃ w, ∀ j, c j w < 0) :
    ∃! z, Minimizes f {z | ∀ j, c j z ≤ 0} z := by
  let cc : Fin q → Unit → E → ℝ := fun j _ z => c j z
  have hKclosed : IsClosed {z | ∀ j, c j z ≤ 0} :=
    feasible_isClosed (c := cc) (x := ()) hc
  have hKconvex : Convex ℝ {z | ∀ j, c j z ≤ 0} :=
    feasible_convex (c := cc) (x := ()) hcconv
  obtain ⟨w, hw⟩ := hslater
  exact existsUnique_minimizer_of_coercive hKclosed
    ⟨w, fun j => (hw j).le⟩ hf.continuousOn
    ((hstrong.strictConvexOn hm).subset (subset_univ _) hKconvex)
    (stronglyConvex_coercive hm hf hstrong)

/-- Continuity at a parameter under finite-dimensional strong convexity and
Slater.  The positive strong-convexity constant may depend on the parameter. -/
theorem optimizer_continuousAt_stronglyConvex
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ}
    {u : X → E} {p : X}
    (hmin : ∀ᶠ x in 𝓝 p, Minimizes (f x) (Feasible c x) (u x))
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hstrong : ∀ x, ∃ m : ℝ, 0 < m ∧ StrongConvexOn univ m (f x))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hcconv : ∀ j, ConvexOn ℝ univ (c j p))
    (hslater : ∃ w, StrictlyFeasible c p w) : ContinuousAt u p := by
  obtain ⟨m, hm, hp⟩ := hstrong p
  apply optimizer_continuousAt_of_coercive hmin hf _ hc hcconv
    (hp.strictConvexOn hm) hslater
    (stronglyConvex_coercive hm (hf.comp (continuous_const.prodMk continuous_id)) hp)
  exact Eventually.of_forall fun x =>
    let ⟨m, hm, hx⟩ := hstrong x
    (hx.strictConvexOn hm).convexOn


theorem optimizer_minimizes [Zero E] {f : E → ℝ} {K : Set E}
    (hex : ∃ z, Minimizes f K z) : Minimizes f K (optimizer f K) := by
  classical
  simp only [optimizer, dif_pos hex]
  exact Classical.choose_spec hex

/-- Local existence, uniqueness, and continuity from Slater at one parameter.
The compactness and coercivity steps are proved above, not assumed here. -/
theorem parametric_optimizer_local
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ} {p : X}
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hstrong : ∀ x, ∃ m : ℝ, 0 < m ∧ StrongConvexOn univ m (f x))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hcconv : ∀ x j, ConvexOn ℝ univ (c j x))
    (hslater : ∃ w, StrictlyFeasible c p w) :
    (∀ᶠ x in 𝓝 p, ∃! z, Minimizes (f x) (Feasible c x) z) ∧
    (∀ᶠ x in 𝓝 p,
      Minimizes (f x) (Feasible c x) (optimizer (f x) (Feasible c x))) ∧
    ContinuousAt (fun x => optimizer (f x) (Feasible c x)) p := by
  obtain ⟨w, hw⟩ := hslater
  have hwNear : ∀ᶠ x in 𝓝 p, StrictlyFeasible c x w :=
    strictlyFeasible_eventually
      (fun j => ((hc j).comp (continuous_id.prodMk continuous_const)).continuousAt) hw
  have hexNear : ∀ᶠ x in 𝓝 p, ∃! z, Minimizes (f x) (Feasible c x) z := by
    filter_upwards [hwNear] with x hx
    obtain ⟨m, hm, hxstrong⟩ := hstrong x
    exact existsUnique_minimizer_stronglyConvex hm
      (hf.comp (continuous_const.prodMk continuous_id)) hxstrong
      (fun j => (hc j).comp (continuous_const.prodMk continuous_id))
      (hcconv x) ⟨w, hx⟩
  have hminNear : ∀ᶠ x in 𝓝 p,
      Minimizes (f x) (Feasible c x) (optimizer (f x) (Feasible c x)) :=
    hexNear.mono fun _ hx => optimizer_minimizes hx.exists
  exact ⟨hexNear, hminNear,
    optimizer_continuousAt_stronglyConvex hminNear hf hstrong hc
      (hcconv p) ⟨w, hw⟩⟩

/-- Global parametric optimizer theorem.  The parameter space may be arbitrary;
the decision space is finite-dimensional. -/
theorem parametric_optimizer_continuous
    [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {q : ℕ} {c : Fin q → X → E → ℝ} {f : X → E → ℝ}
    (hf : Continuous (fun a : X × E => f a.1 a.2))
    (hstrong : ∀ x, ∃ m : ℝ, 0 < m ∧ StrongConvexOn univ m (f x))
    (hc : ∀ j, Continuous (fun a : X × E => c j a.1 a.2))
    (hcconv : ∀ x j, ConvexOn ℝ univ (c j x))
    (hslater : ∀ x, ∃ w, StrictlyFeasible c x w) :
    (∀ x, ∃! z, Minimizes (f x) (Feasible c x) z) ∧
    (∀ x, Minimizes (f x) (Feasible c x) (optimizer (f x) (Feasible c x))) ∧
    Continuous (fun x => optimizer (f x) (Feasible c x)) := by
  have hlocal (x : X) := parametric_optimizer_local hf hstrong hc hcconv (hslater x)
  exact ⟨fun x => (hlocal x).1.self_of_nhds,
    fun x => (hlocal x).2.1.self_of_nhds,
    continuous_iff_continuousAt.2 fun x => (hlocal x).2.2⟩

end CBFIndependence.Optimization
