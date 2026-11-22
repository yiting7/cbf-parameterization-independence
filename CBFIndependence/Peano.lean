import CBFIndependence.CompactTrajectories
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Tactic

/-!
# Peano local existence for continuous finite-dimensional vector fields

The vector field is approximated uniformly on a compact ball by smooth fields.
Picard–Lindelöf provides approximate solutions on a common time interval determined
by a uniform speed bound.  Arzelà–Ascoli and uniform convergence of derivatives
then produce a solution of the continuous field, without a Lipschitz assumption.
-/

namespace CBFIndependence

open Set Filter Metric Topology
open scoped NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Uniform smooth approximation on an arbitrary compact set. -/
theorem continuous_smooth_approx_on_compact {F : E → E}
    (hF : Continuous F) {K : Set E} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : E → E, ContDiff ℝ ∞ G ∧ ∀ x ∈ K, dist (G x) (F x) < ε := by
  have hu : UniformContinuousOn F (cthickening 1 K) :=
    hK.cthickening.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.mp hu (ε / 2) (half_pos hε)
  obtain ⟨G, hG, happrox⟩ :=
    hF.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (lt_min one_pos hδ)
  refine ⟨G, hG, ?_⟩
  intro x hx
  apply (happrox x (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  rw [mem_ball, lt_min_iff] at hy
  exact (hfδ y (mem_cthickening_of_dist_le _ x _ _ hx hy.1.le)
    x (self_subset_cthickening _ hx) hy.2).le

/-- A smooth field is Lipschitz on a compact convex ball. -/
theorem smooth_lipschitz_on_closedBall {G : E → E}
    (hG : ContDiff ℝ ∞ G) (x : E) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L G (closedBall x r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    (hG.continuous_fderiv (by simp)).continuousOn
  refine ⟨Real.toNNReal M, ?_⟩
  apply (convex_closedBall x r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun y _ => ((hG.differentiable (by simp)) y).hasFDerivAt.hasFDerivWithinAt)
  intro y hy
  exact_mod_cast (hM y hy).trans (Real.le_coe_toNNReal M)

/-- The Picard construction includes a uniform ball bound.  This wrapper keeps
that bound, which the more concise library existence statement omits. -/
theorem picard_bounded_solution {f : ℝ → E → E} {a b : ℝ}
    {t₀ : Icc a b} {x₀ x : E} {r₀ r L K : ℝ≥0}
    (hf : IsPicardLindelof f t₀ x₀ r₀ r L K) (hx : x ∈ closedBall x₀ r) :
    ∃ γ : ℝ → E, γ t₀ = x ∧ (∀ t, γ t ∈ closedBall x₀ r₀) ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt γ (f t (γ t)) (Icc a b) t := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, fun _ => α.compProj_mem_closedBall hf.mul_max_le, ?_⟩
  · rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]


/-- Peano local existence, with an arbitrary absolute initial time.
The field is only continuous; uniqueness is neither assumed nor asserted. -/
theorem continuous_exists_local_forward_solution {F : E → E}
    (hF : Continuous F) (a : ℝ) (x₀ : E) :
    ∃ b > a, ∃ γ : ℝ → E, γ a = x₀ ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt γ (F (γ t)) (Ici a) t := by
  classical
  let K := closedBall x₀ (1 : ℝ)
  have hK : IsCompact K := isCompact_closedBall x₀ 1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  let L : ℝ≥0 := Real.toNNReal M + 1
  have hL : 0 < (L : ℝ) := by dsimp [L]; positivity
  let d : ℝ := 1 / (L : ℝ)
  have hdpos : 0 < d := one_div_pos.mpr hL
  let b : ℝ := a + d
  have hab : a < b := by dsimp [b]; linarith
  let t₀ : Icc a b := ⟨a, le_rfl, hab.le⟩
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεone (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
    simp only [one_mul]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose G hG hGap using fun n => continuous_smooth_approx_on_compact hF hK (hεpos n)
  choose C hC using fun n => smooth_lipschitz_on_closedBall (hG n) x₀ 1
  have hGbound (n : ℕ) (x : E) (hx : x ∈ K) : ‖G n x‖ ≤ (L : ℝ) := by
    have htriangle : ‖G n x‖ ≤ ‖G n x - F x‖ + ‖F x‖ := by
      calc
        ‖G n x‖ = ‖(G n x - F x) + F x‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have herror : ‖G n x - F x‖ < ε n := by
      simpa only [dist_eq_norm] using hGap n x hx
    have hLM : M + 1 ≤ (L : ℝ) := by
      dsimp [L]
      exact add_le_add_right (le_max_left M 0) 1
    linarith [hM x hx, hεone n]
  have hpl (n : ℕ) :
      IsPicardLindelof (fun _ => G n) t₀ x₀ 1 0 L (C n) := by
    apply IsPicardLindelof.of_time_independent (hGbound n) (hC n)
    change (L : ℝ) * max (b - a) (a - a) ≤ (1 : ℝ) - 0
    have hba : b - a = d := by dsimp [b]; ring
    rw [hba, sub_self, sub_zero, max_eq_left hdpos.le]
    dsimp [d]
    rw [mul_one_div_cancel hL.ne']
  choose z hzinit hzrange hzderiv using fun n =>
    picard_bounded_solution (hpl n) (mem_closedBall_self (le_refl (0 : ℝ)))
  have hzlip (n : ℕ) : LipschitzOnWith L (z n) (Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hzderiv n)
    intro t ht
    exact_mod_cast hGbound n (z n t) (hzrange n t)
  obtain ⟨g, φ, hφ, hg⟩ := trajectory_subsequence hK
    (fun n t _ => hzrange n t) hzlip
  have hgcont : ContinuousOn g (Icc a b) :=
    hg.continuousOn (.of_forall fun n => (hzlip (φ n)).continuousOn)
  have hgrange : ∀ t ∈ Icc a b, g t ∈ K := by
    intro t ht
    exact hK.isClosed.mem_of_tendsto (hg.tendsto_at ht)
      (.of_forall fun n => hzrange (φ n) t)
  have hFg : TendstoUniformlyOn (fun n t => F (z (φ n) t))
      (fun t => F (g t)) atTop (Icc a b) :=
    UniformContinuousOn.comp_tendstoUniformlyOn_eventually
      (.of_forall fun n t _ => hzrange (φ n) t) hgrange
      (hK.uniformContinuousOn_of_continuous hF.continuousOn) hg
  have hεφ : Tendsto (fun n => ε (φ n)) atTop (𝓝 0) :=
    hεlim.comp hφ.tendsto_atTop
  have hderivlim : TendstoUniformlyOn (fun n t => G (φ n) (z (φ n) t))
      (fun t => F (g t)) atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hFg) (η / 2) (half_pos hη),
      hεφ.eventually (gt_mem_nhds (half_pos hη))] with n hn he
    intro t ht
    calc
      dist (F (g t)) (G (φ n) (z (φ n) t)) ≤
          dist (F (g t)) (F (z (φ n) t)) +
            dist (F (z (φ n) t)) (G (φ n) (z (φ n) t)) := dist_triangle _ _ _
      _ < η / 2 + η / 2 := add_lt_add (hn t ht) (by
        rw [dist_comm]
        exact (hGap (φ n) _ (hzrange (φ n) t)).trans he)
      _ = η := by ring
  have hgderiv : ∀ t ∈ Ioo a b, HasDerivAt g (F (g t)) t := by
    intro t ht
    apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo
      (hderivlim.mono Ioo_subset_Icc_self)
      (.of_forall (fun n s hs =>
        (hzderiv (φ n) s (Ioo_subset_Icc_self hs)).hasDerivAt
          (Icc_mem_nhds hs.1 hs.2)))
      (fun s hs => hg.tendsto_at (Ioo_subset_Icc_self hs)) ht
  have hginit : g a = x₀ := by
    have hlim := hg.tendsto_at (left_mem_Icc.mpr hab.le)
    have hcst : Tendsto (fun n => z (φ n) a) atTop (𝓝 x₀) := by
      have heq : (fun n => z (φ n) a) = (fun _ : ℕ => x₀) :=
        funext fun n => hzinit (φ n)
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim hcst
  have hginitialderiv : HasDerivWithinAt g (F (g a)) (Ici a) a :=
    segment_initial_derivative hab hgcont
      (hF.continuousOn.comp hgcont (fun _ _ => mem_univ _)) hgderiv
  refine ⟨b, hab, g, hginit, ?_⟩
  intro t ht
  by_cases hta : t = a
  · subst t
    exact hginitialderiv
  · exact (hgderiv t ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩).hasDerivWithinAt


/-- Local Peano existence on an open domain.  The trajectory stays in the
domain, and no continuity of the field outside that domain is assumed. -/
theorem continuousOn_exists_local_forward_solution {F : E → E} {U : Set E}
    (hU : IsOpen U) (hF : ContinuousOn F U) (a : ℝ) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ b > a, ∃ γ : ℝ → E, γ a = x₀ ∧
      (∀ t ∈ Ico a b, γ t ∈ U) ∧
      ∀ t ∈ Ico a b, HasDerivWithinAt γ (F (γ t)) (Ici a) t := by
  classical
  letI : TietzeExtension E := TietzeExtension.of_tvs ℝ
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall x₀ r ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRU
  let fK : C(closedBall x₀ r, E) :=
    ⟨fun x => F x, continuousOn_iff_continuous_restrict.mp (hF.mono hclosed)⟩
  obtain ⟨G, hG⟩ := fK.exists_restrict_eq isClosed_closedBall
  have heq : ∀ x ∈ closedBall x₀ r, G x = F x := by
    intro x hx
    exact congrArg (fun h : C(closedBall x₀ r, E) => h ⟨x, hx⟩) hG
  obtain ⟨b, hab, γ, hinit, hderiv⟩ :=
    continuous_exists_local_forward_solution G.continuous a x₀
  have hγcont : ContinuousWithinAt γ (Ici a) a :=
    (hderiv a ⟨le_rfl, hab⟩).continuousWithinAt
  have hball : ball x₀ r ∈ 𝓝 (γ a) := by
    rw [hinit]
    exact ball_mem_nhds x₀ hr
  have hnear : ∀ᶠ t in 𝓝[Ici a] a, γ t ∈ ball x₀ r :=
    hγcont.tendsto.eventually hball
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let b' := min b (a + δ / 2)
  have hab' : a < b' := lt_min hab (by linarith)
  have hinside : ∀ t ∈ Ico a b', γ t ∈ ball x₀ r := by
    intro t ht
    apply hδsmall
    refine ⟨?_, ht.1⟩
    change dist t a < δ
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have htupper := ht.2.trans_le (min_le_right b (a + δ / 2))
    linarith
  refine ⟨b', hab', γ, hinit, ?_, ?_⟩
  · intro t ht
    exact hclosed (ball_subset_closedBall (hinside t ht))
  · intro t ht
    have hd := hderiv t ⟨ht.1, ht.2.trans_le (min_le_left b (a + δ / 2))⟩
    rw [heq _ (ball_subset_closedBall (hinside t ht))] at hd
    exact hd

end CBFIndependence

