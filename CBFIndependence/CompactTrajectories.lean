import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

namespace CBFIndependence
open Set Filter Metric Topology BoundedContinuousFunction
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Arzelà–Ascoli on a closed time interval in the form needed for ODE solution segments. -/
theorem trajectory_subsequence {a b : ℝ} {K : Set E} (hK : IsCompact K)
    {z : ℕ → ℝ → E} (inK : ∀ n t, t ∈ Icc a b → z n t ∈ K) {M : ℝ≥0}
    (lip : ∀ n, LipschitzOnWith M (z n) (Icc a b)) :
    ∃ g : ℝ → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => z (φ n)) g atTop (Icc a b) := by
  classical
  let Z (n : ℕ) : (Icc a b) →ᵇ E := mkOfCompact
    ⟨fun t => z n t, continuousOn_iff_continuous_restrict.mp (lip n).continuousOn⟩
  have he : Equicontinuous ((↑) : range Z → (Icc a b) → E) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (M : ℝ) * r)
    · simpa using (tendsto_const_nhds (x := (M : ℝ))).mul (tendsto_id (x := 𝓝 (0 : ℝ)))
    · intro t s f
      obtain ⟨n, hn⟩ := f.property
      rw [← hn]
      exact (lip n).dist_le_mul t t.property s s.property
  have hc := arzela_ascoli K hK (range Z) (by
    rintro f t ⟨n, rfl⟩
    exact inK n t t.property) he
  obtain ⟨G, _, φ, hφ, hG⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  let g (t : ℝ) : E := if h : t ∈ Icc a b then G ⟨t,h⟩ else 0
  refine ⟨g, φ, hφ, Metric.tendstoUniformlyOn_iff.mpr ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hG) ε hε] with n hn
  intro t ht
  have hdist := dist_coe_le_dist (f := Z (φ n)) (g := G) (⟨t, ht⟩ : Icc a b)
  have hgt : g t = G ⟨t,ht⟩ := dif_pos ht
  rw [hgt, dist_comm]
  exact hdist.trans_lt hn

/-- A uniform limit of perturbed trajectories solves the unperturbed ODE in the
interior of the time interval. The field only needs continuity on the compact
set containing the state and perturbation. -/
theorem derivative_limit_of_vanishing_normal {a b : ℝ}
    {K : Set (E × ℝ)} (hK : IsCompact K) {B : E × ℝ → E} (hB : ContinuousOn B K)
    {z : ℕ → ℝ → E} {r : ℕ → ℝ → ℝ} {g : ℝ → E}
    (hz : TendstoUniformlyOn z g atTop (Icc a b))
    (hr : TendstoUniformlyOn r (fun _ => 0) atTop (Icc a b))
    (rangeK : ∀ n t, t ∈ Icc a b → (z n t, r n t) ∈ K)
    (hd : ∀ n t, t ∈ Ioo a b → HasDerivAt (z n) (B (z n t, r n t)) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt g (B (g t, 0)) t := by
  have hpair : TendstoUniformlyOn (fun n t => (z n t, r n t))
      (fun t => (g t, (0 : ℝ))) atTop (Icc a b) :=
    fun u hu => ((hz.prodMk hr) u hu).diag_of_prod
  have hg : ∀ t ∈ Icc a b, (g t, (0 : ℝ)) ∈ K := by
    intro s hs
    exact hK.isClosed.mem_of_tendsto (hpair.tendsto_at hs)
      (.of_forall (fun n => rangeK n s hs))
  have hu := UniformContinuousOn.comp_tendstoUniformlyOn_eventually
    (.of_forall rangeK) hg (hK.uniformContinuousOn_of_continuous hB) hpair
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hu.mono Ioo_subset_Icc_self)
    (.of_forall hd) (fun s hs => hz.tendsto_at (Ioo_subset_Icc_self hs)) ht

/-- Finite-horizon compactness with a continuous field. The speed bound and
the equicontinuity needed by Arzelà–Ascoli are both derived from the ODE. -/
theorem compact_solution_segments {a b : ℝ} {K : Set (E × ℝ)} (hK : IsCompact K)
    {B : E × ℝ → E} (hB : ContinuousOn B K)
    {z : ℕ → ℝ → E} {r : ℕ → ℝ → ℝ}
    (hr : TendstoUniformlyOn r (fun _ => 0) atTop (Icc a b))
    (rangeK : ∀ n t, t ∈ Icc a b → (z n t, r n t) ∈ K)
    (hd : ∀ n t, t ∈ Icc a b →
      HasDerivWithinAt (z n) (B (z n t, r n t)) (Icc a b) t) :
    ∃ g : ℝ → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformlyOn (fun n => z (φ n)) g atTop (Icc a b) ∧
      ContinuousOn g (Icc a b) ∧
      (∀ t ∈ Icc a b, (g t, (0 : ℝ)) ∈ K) ∧
      ∀ t ∈ Ioo a b, HasDerivAt g (B (g t, 0)) t := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hB
  have lip (n : ℕ) : LipschitzOnWith (Real.toNNReal M) (z n) (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hd n)
    intro t ht
    exact_mod_cast (hM _ (rangeK n t ht)).trans (Real.le_coe_toNNReal M)
  obtain ⟨g, φ, hφ, hg⟩ := trajectory_subsequence (hK.image continuous_fst)
    (fun n t ht => ⟨_, rangeK n t ht, rfl⟩) lip
  have hn := hr.seq_tendstoUniformlyOn φ hφ.tendsto_atTop
  refine ⟨g, φ, hφ, hg, hg.continuousOn (.of_forall (fun n => (lip (φ n)).continuousOn)), ?_, ?_⟩
  · intro t ht
    exact hK.isClosed.mem_of_tendsto ((hg.tendsto_at ht).prodMk_nhds (hn.tendsto_at ht))
      (.of_forall (fun n => rangeK (φ n) t ht))
  · intro t ht
    apply derivative_limit_of_vanishing_normal hK hB hg hn (fun n => rangeK (φ n)) _ ht
    intro n s hs
    exact (hd (φ n) s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)

/-- The right derivative of a limiting solution at its initial time.
Continuity of the right-hand side is only needed along the limiting curve. -/
theorem segment_initial_derivative {a b : ℝ} (hab : a < b) {g v : ℝ → E}
    (hg : ContinuousOn g (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt g (v t) t) :
    HasDerivWithinAt g (v a) (Ici a) a := by
  have hs : Ioo a b ∈ 𝓝[>] a := Ioo_mem_nhdsGT hab
  apply hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo a b)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    ((hg a (left_mem_Icc.mpr hab.le)).mono Ioo_subset_Icc_self) hs
  have hv' : Tendsto v (𝓝[>] a) (𝓝 (v a)) := by
    apply (hv a (left_mem_Icc.mpr hab.le)).tendsto.mono_left
    exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (mem_of_superset hs Ioo_subset_Icc_self))
  apply hv'.congr'
  filter_upwards [hs] with t ht using (hd t ht).deriv.symm

/-- If no unforced segment inside a compact set connects the closed sets A and
D, small normal forcing also precludes such a segment. To model a variable
stopping time τ, use (z,τ) as state on [0,1], with τ'=0 and z'=τ B(z,r). -/
theorem robust_segment_endpoint {a b : ℝ} (hab : a < b)
    {K : Set (E × ℝ)} (hK : IsCompact K)
    {A D : Set E} (hA : IsClosed A) (hD : IsClosed D)
    {B : E × ℝ → E} (hB : ContinuousOn B K)
    (separated : ∀ g : ℝ → E, ContinuousOn g (Icc a b) →
      (∀ t ∈ Icc a b, (g t, (0 : ℝ)) ∈ K) →
      (∀ t ∈ Ioo a b, HasDerivAt g (B (g t, 0)) t) → g a ∈ A → g b ∉ D) :
    ∃ η > (0 : ℝ), ∀ z : ℝ → E, ∀ r : ℝ → ℝ,
      (∀ t ∈ Icc a b, |r t| ≤ η) →
      (∀ t ∈ Icc a b, (z t, r t) ∈ K) →
      (∀ t ∈ Icc a b, HasDerivWithinAt z (B (z t, r t)) (Icc a b) t) →
      z a ∈ A → z b ∉ D := by
  classical
  by_contra! hn
  have hn' (n : ℕ) := hn (1 / ((n:ℝ)+1)) (by positivity)
  choose z r hr hKz hd ha hb using hn'
  have hsmall : TendstoUniformlyOn r (fun _ => 0) atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hε)]
      with n hnε
    intro t ht
    simpa [Real.dist_eq, abs_neg] using (hr n t ht).trans_lt hnε
  obtain ⟨g, φ, _, hconv, hg, hKg, dg⟩ := compact_solution_segments hK hB hsmall hKz hd
  have hga := hA.mem_of_tendsto (hconv.tendsto_at (left_mem_Icc.mpr hab.le))
    (.of_forall (fun n => ha (φ n)))
  exact separated g hg hKg dg hga (hD.mem_of_tendsto
    (hconv.tendsto_at (right_mem_Icc.mpr hab.le)) (.of_forall (fun n => hb (φ n))))

end CBFIndependence
