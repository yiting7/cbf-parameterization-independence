import CBFIndependence.MaximalExtension
import CBFIndependence.TimeBlocks

namespace CBFIndependence
open Set Filter Topology Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Undo the change of clock on a positive-length reference segment.
A maximal extension with infinite lifetime agrees even at the right endpoint,
which is not in the domain of the original half-open forward solution. -/
theorem reference_segment_extension_on {L : ℝ} (hL : 0 < L) {g : ℝ → E} {F : E → E}
    {D : Set E} (hin : MapsTo g (Icc 0 1) D)
    (hg : ContinuousOn g (Icc 0 1)) (hv : ContinuousOn (fun t => F (g t)) (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (L • F (g t)) t)
    (complete : ∀ d ∈ MaximalSolutionsOn F D, d.curve 0 = g 0 → d.IsGlobal) :
    ∃ d ∈ MaximalSolutionsOn F D, d.curve 0 = g 0 ∧ d.curve L = g 1 := by
  let c : ForwardCurve E :=
    ⟨fun t => g (L⁻¹*t), ENNReal.ofReal L, ENNReal.ofReal_pos.mpr hL⟩
  have hr t (ht : t ∈ Ico (0 : ℝ) L) : L⁻¹*t ∈ Ico (0 : ℝ) 1 := by
    constructor
    · exact mul_nonneg (inv_nonneg.mpr hL.le) ht.1
    · simpa [← div_eq_inv_mul] using (div_lt_one hL).mpr ht.2
  have hn t (ht : 0 ≤ t) : 0 ≤ L⁻¹*t := mul_nonneg (inv_nonneg.mpr hL.le) ht
  have solve : SolvesODE F c := by
    intro t ht
    have hi := hr t ⟨ht.1,(ENNReal.ofReal_lt_ofReal_iff hL).mp ht.2⟩
    have der : HasDerivWithinAt g (L • F (g (L⁻¹*t))) (Ici 0) (L⁻¹*t) := by
      rcases hi.1.eq_or_lt with he|he
      · rw [← he]
        exact segment_initial_derivative zero_lt_one hg (continuousOn_const.smul hv) hd
      · exact (hd _ ⟨he,hi.2⟩).hasDerivWithinAt
    have clock : HasDerivWithinAt (fun t : ℝ => L⁻¹*t) L⁻¹ (Ici 0) t := by
      simpa using ((hasDerivAt_id t).const_mul L⁻¹).hasDerivWithinAt (s := Ici 0)
    simpa [c, Function.comp_def, smul_smul, hL.ne'] using der.scomp t clock hn
  have solveOn : SolvesODEOn F D c := by
    refine ⟨solve, ?_⟩
    intro t ht
    exact hin (Ico_subset_Icc_self (hr t ⟨ht.1,(ENNReal.ofReal_lt_ofReal_iff hL).mp ht.2⟩))
  obtain ⟨d, extd, hm⟩ := MaximalExtension.exists_maximal_extension_on solveOn
  have hstart : d.curve 0 = g 0 := by simpa [c] using extd.2 0 c.zero_inDomain
  have full := complete d hm hstart
  have hc : ContinuousOn d.curve (Icc 0 L) := by
    intro t ht
    exact (hm.1.1 t (d.inDomain_of_global full ht.1)).continuousWithinAt.mono Icc_subset_Ici_self
  have htime : MapsTo (fun t : ℝ => L⁻¹*t) (Icc 0 L) (Icc 0 1) := by
    intro t ht
    exact ⟨hn t ht.1, by simpa [← div_eq_inv_mul] using (div_le_one hL).mpr ht.2⟩
  have he : EqOn d.curve (fun t => g (L⁻¹*t)) (Ico 0 L) := by
    intro t ht
    exact extd.2 t ⟨ht.1,(ENNReal.ofReal_lt_ofReal_iff hL).mpr ht.2⟩
  have he' := he.of_subset_closure hc
    (hg.comp (continuous_const.mul continuous_id).continuousOn htime) Ico_subset_Icc_self
    (by rw [closure_Ico hL.ne])
  exact ⟨d,hm,hstart,by simpa [hL.ne'] using he' (right_mem_Icc.mpr hL.le)⟩

/-- Finite-time estimate for the exact reference paths selected by a closed
observation graph. D may be the boundary intersected with an open ball. -/
theorem reference_block_test {F : E → E} {D Q A : Set E} {h : E → ℝ} {B : E × ℝ → E}
    {e d T : ℝ} (hT : 0 < T) (hF : ContinuousOn F D)
    (slice : ∀ x ∈ Q, h x = 0 → x ∈ D ∧ B (x,0) = F x)
    (start : ∀ z ∈ A, ‖z‖ < e)
    (est : ∀ c ∈ MaximalSolutionsOn F D, c.curve 0 ∈ A → h (c.curve 0) = 0 →
      c.IsGlobal ∧ (∀ t ≥ 0, ‖c.curve t‖ < e) ∧ ‖c.curve T‖ < d) :
    ∀ L ∈ Icc 0 T, ∀ g : ℝ → E, ContinuousOn g (Icc 0 1) →
      (∀ t ∈ Icc (0:ℝ) 1, g t ∈ Q ∧ h (g t) = 0) →
      (∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (L • B (g t,0)) t) →
      g 0 ∈ A → ‖g 1‖ < e ∧ (L = T → ‖g 1‖ < d) := by
  intro L hL g hg hq hd hinit
  rcases hL.1.eq_or_lt with hzero|hpos
  · subst L
    have he := segment_constant hg (fun t ht => by simpa using hd t ht)
    rw [he 1 (right_mem_Icc.mpr zero_le_one)]
    exact ⟨start _ hinit,fun hz => (hT.ne hz).elim⟩
  have hi t (ht : t ∈ Icc (0:ℝ) 1) := slice _ (hq t ht).1 (hq t ht).2
  have hstart := (hq 0 (left_mem_Icc.mpr zero_le_one)).2
  obtain ⟨c,hc,hc₀,hcL⟩ := reference_segment_extension_on hpos
    (fun t ht => (hi t ht).1) hg (hF.comp hg (fun t ht => (hi t ht).1))
    (fun t ht => by simpa only [(hi t (Ioo_subset_Icc_self ht)).2] using hd t ht)
    (fun c hc hc₀ => (est c hc (hc₀ ▸ hinit) (hc₀ ▸ hstart)).1)
  obtain ⟨_,hstay,hend⟩ := est c hc (hc₀ ▸ hinit) (hc₀ ▸ hstart)
  rw [← hcL]
  exact ⟨hstay L hL.1, fun hh => by simpa only [hh] using hend⟩

end CBFIndependence
