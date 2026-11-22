import CBFIndependence.CompactTrajectories
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# One subsequence on all finite time intervals

The construction takes the product of the compact Arzelà–Ascoli closures on
integer time windows.  Countability of the product permits sequential compactness.
Agreement of the component limits follows from uniqueness of pointwise limits.
-/

namespace CBFIndependence

open Set Filter Metric Topology BoundedContinuousFunction
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E]

/-- Compactness on the half-line: one subsequence converges uniformly on every
finite time interval.  No completeness assumption on the ambient space is needed
because all values lie in the given compact set. -/
theorem trajectory_subsequence_locally_uniform
    {K : Set E} (hK : IsCompact K) {z : ℕ → ℝ → E}
    (inK : ∀ n t, 0 ≤ t → z n t ∈ K) {M : ℝ≥0}
    (lip : ∀ n, LipschitzOnWith M (z n) (Ici 0)) :
    ∃ g : ℝ → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ T : ℝ, 0 ≤ T →
        TendstoUniformlyOn (fun n => z (φ n)) g atTop (Icc 0 T) := by
  classical
  let W (m : ℕ) := Icc (0 : ℝ) (m : ℝ)
  let Z (m n : ℕ) : W m →ᵇ E := mkOfCompact
    ⟨fun t => z n t,
      continuousOn_iff_continuous_restrict.mp
        ((lip n).mono Icc_subset_Ici_self).continuousOn⟩
  have he (m : ℕ) : Equicontinuous ((↑) : range (Z m) → W m → E) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (M : ℝ) * r)
    · simpa using (tendsto_const_nhds (x := (M : ℝ))).mul
        (tendsto_id (x := 𝓝 (0 : ℝ)))
    · intro t s f
      obtain ⟨n, hn⟩ := f.property
      rw [← hn]
      exact (lip n).dist_le_mul t t.property.1 s s.property.1
  have hc (m : ℕ) : IsCompact (closure (range (Z m))) :=
    arzela_ascoli K hK (range (Z m))
      (by
        rintro f t ⟨n, rfl⟩
        exact inK n t t.property.1) (he m)
  let P (n : ℕ) : ∀ m : ℕ, W m →ᵇ E := fun m => Z m n
  have hprod :
      IsCompact {G : ∀ m : ℕ, W m →ᵇ E | ∀ m, G m ∈ closure (range (Z m))} :=
    isCompact_pi_infinite hc
  obtain ⟨G, _hGin, φ, hφ, hG⟩ := hprod.tendsto_subseq
    (show ∀ n, P n ∈ {G : ∀ m : ℕ, W m →ᵇ E |
      ∀ m, G m ∈ closure (range (Z m))} from
      fun n m => subset_closure (mem_range_self n))
  have hcomponent (m : ℕ) :
      Tendsto (fun n => Z m (φ n)) atTop (𝓝 (G m)) := by
    exact ((continuous_apply m).continuousAt.tendsto).comp hG
  have hvalue (m : ℕ) (t : W m) :
      Tendsto (fun n => z (φ n) t) atTop (𝓝 (G m t)) := by
    exact continuous_eval_const.continuousAt.tendsto.comp (hcomponent m)
  let g (t : ℝ) : E :=
    if ht : 0 ≤ t then G (Nat.ceil t) ⟨t, ht, Nat.le_ceil t⟩ else 0
  have hgeq (m : ℕ) (t : ℝ) (ht : t ∈ W m) :
      g t = G m ⟨t, ht⟩ := by
    dsimp only [g]
    rw [dif_pos ht.1]
    exact tendsto_nhds_unique
      (hvalue (Nat.ceil t) ⟨t, ht.1, Nat.le_ceil t⟩) (hvalue m ⟨t, ht⟩)
  refine ⟨g, φ, hφ, ?_⟩
  intro T _hT
  let m := Nat.ceil T
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp (hcomponent m)) ε hε] with n hn
  intro t ht
  have htm : t ∈ W m := ⟨ht.1, ht.2.trans (Nat.le_ceil T)⟩
  rw [hgeq m t htm, dist_comm]
  exact (dist_coe_le_dist (f := Z m (φ n)) (g := G m) ⟨t, htm⟩).trans_lt hn

end CBFIndependence

