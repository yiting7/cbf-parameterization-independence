import CBFIndependence.CompactTrajectories
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace CBFIndependence
open Filter Set Metric Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem segment_constant {u : ℝ → E} (hu : ContinuousOn u (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt u 0 t) :
    ∀ t ∈ Icc (0 : ℝ) 1, u t = u 0 := by
  obtain ⟨c, h⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv)
  have he : EqOn u (fun _ => c) (Ioo 0 1) := h
  have hc := he.of_subset_closure hu continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)])
  exact fun _ ht => (hc ht).trans (hc (left_mem_Icc.mpr zero_le_one)).symm

/-- A single disturbance tolerance works for every stopping time L ∈ [0,T].
The reference hypothesis tests only exact, unforced solutions on [0,1] with
the time variable rescaled by L. Bad endpoints may depend on the elapsed time. -/
theorem robust_stopped_segments {T : ℝ} {Q A : Set E} {bad : Set (E × ℝ)}
    (compactQ : IsCompact Q) (closedA : IsClosed A) (closedBad : IsClosed bad)
    {R : ℝ} {B : E × ℝ → E} (hB : ContinuousOn B (Q ×ˢ Icc (-R) R))
    {C : Set (E × ℝ)} (closedC : IsClosed C)
    (safe : ∀ L ∈ Icc 0 T, ∀ g : ℝ → E, ContinuousOn g (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, g t ∈ Q ∧ (g t, (0 : ℝ)) ∈ C) →
      (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (L • B (g t, 0)) t) →
      g 0 ∈ A → (g 1,L) ∉ bad) :
    ∃ η > (0 : ℝ), ∀ L ∈ Icc 0 T, ∀ z : ℝ → E, ∀ r : ℝ → ℝ,
      (∀ t ∈ Icc 0 L, |r t| ≤ η) →
      (∀ t ∈ Icc 0 L, (z t, r t) ∈ (Q ×ˢ Icc (-R) R) ∩ C) →
      (∀ t ∈ Icc 0 L, HasDerivWithinAt z (B (z t, r t)) (Icc 0 L) t) →
      z 0 ∈ A → (z L,L) ∉ bad := by
  let K := ((Q ×ˢ Icc (0 : ℝ) T) ×ˢ Icc (-R) R) ∩
    (fun x : (E × ℝ) × ℝ => (x.1.1,x.2)) ⁻¹' C
  let field (x : (E × ℝ) × ℝ) : E × ℝ := (x.1.2 • B (x.1.1,x.2),0)
  have hK : IsCompact K := ((compactQ.prod isCompact_Icc).prod isCompact_Icc).inter_right
    (closedC.preimage (continuous_fst.fst.prodMk continuous_snd))
  have cont : ContinuousOn field K := by
    have hmap : MapsTo (fun x : (E × ℝ) × ℝ => (x.1.1,x.2)) K (Q ×ˢ Icc (-R) R) :=
      fun _ hx => ⟨hx.1.1.1,hx.1.2⟩
    exact (continuous_fst.snd.continuousOn.smul (hB.comp
      ((continuous_fst.fst.prodMk continuous_snd).continuousOn) hmap)).prodMk continuousOn_const
  obtain ⟨η, hη, bound⟩ := robust_segment_endpoint zero_lt_one hK
    (closedA.prod (isClosed_Icc (a := (0:ℝ)) (b := T))) closedBad cont (by
      intro g hg hr hd ha
      have hclock := segment_constant hg.snd (fun t ht =>
        (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t (hd t ht))
      have hz : ∀ t ∈ Ioo (0 : ℝ) 1,
          HasDerivAt (fun s => (g s).1) ((g 0).2 • B ((g t).1,0)) t := by
        intro t ht
        have h := (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t (hd t ht)
        change HasDerivAt (fun s => (g s).1) ((g t).2 • B ((g t).1,0)) t at h
        rwa [hclock t (Ioo_subset_Icc_self ht)] at h
      have hend := safe (g 0).2 ha.2 (fun t => (g t).1) hg.fst
        (fun t ht => ⟨(hr t ht).1.1.1,(hr t ht).2⟩) hz ha.1
      simpa only [← hclock 1 (right_mem_Icc.mpr zero_le_one), Prod.mk.eta] using hend)
  refine ⟨η,hη,?_⟩
  intro L hL z r hsmall hin hd hstart
  have maps : MapsTo (fun t : ℝ => L*t) (Icc 0 1) (Icc 0 L) := by
    intro t ht
    exact ⟨mul_nonneg hL.1 ht.1, (mul_le_mul_of_nonneg_left ht.2 hL.1).trans_eq (mul_one L)⟩
  have hbad := bound (fun t => (z (L*t),L)) (fun t => r (L*t))
    (fun _ ht => hsmall _ (maps ht))
    (fun _ ht => ⟨⟨⟨(hin _ (maps ht)).1.1,hL⟩,(hin _ (maps ht)).1.2⟩,(hin _ (maps ht)).2⟩)
    (by
      intro t ht
      have htime : HasDerivWithinAt (fun t : ℝ => L*t) L (Icc 0 1) t := by
        simpa using ((hasDerivAt_id t).const_mul L).hasDerivWithinAt (s := Icc 0 1)
      have h := (hd _ (maps ht)).scomp t htime maps
      exact h.prodMk (hasDerivWithinAt_const _ _ _))
    (by simpa using And.intro hstart hL)
  simpa using hbad

/-- A first contact exists for a continuous path that goes from below to at or
above a level. This supplies a closed, compact time segment prior to escape. -/
theorem first_contact {u : ℝ → ℝ} {t R : ℝ} (ht : 0 ≤ t)
    (cont : ContinuousOn u (Icc 0 t)) (start : u 0 < R) (finish : R ≤ u t) :
    ∃ s ∈ Ioc 0 t, u s = R ∧ ∀ v ∈ Icc 0 s, u v ≤ R := by
  let K := Icc 0 t ∩ u ⁻¹' {R}
  have closedK : IsClosed K := cont.preimage_isClosed_of_isClosed isClosed_Icc
    (isClosed_singleton (x := R))
  have compactK : IsCompact K := isCompact_Icc.of_isClosed_subset closedK inter_subset_left
  obtain ⟨s, hs, hv⟩ := intermediate_value_Icc ht cont ⟨start.le,finish⟩
  obtain ⟨s₀, h₀, least⟩ := compactK.exists_isLeast ⟨s,hs,hv⟩
  have hval : u s₀ = R := h₀.2
  have hpos : 0 < s₀ := lt_of_le_of_ne h₀.1.1 (fun e => start.ne (e.symm ▸ hval))
  refine ⟨s₀, ⟨hpos,h₀.1.2⟩,hval,?_⟩
  intro v hv
  by_contra! he
  have hlt : v < s₀ := lt_of_le_of_ne hv.2 (fun e => he.ne' (e.symm ▸ hval))
  have inc : Icc 0 v ⊆ Icc 0 t := Icc_subset_Icc_right (hv.2.trans h₀.1.2)
  obtain ⟨v', hv', e⟩ := intermediate_value_Icc hv.1 (cont.mono inc) ⟨start.le,he.le⟩
  exact (lt_of_le_of_lt hv'.2 hlt).not_ge (least ⟨inc hv',e⟩)

/-- A finite-time return estimate for every perturbed trajectory, including
trajectories for which no state bound has been assumed. The first contact with
the outer sphere would itself be a forbidden endpoint of a confined segment. -/
theorem robust_return_block [ProperSpace E] {A : Set E} (hA : IsClosed A)
    {T R e d : ℝ} (hR : 0 < R) (start : ∀ z ∈ A, ‖z‖ < e)
    {B : E × ℝ → E} (hB : ContinuousOn B (closedBall 0 e ×ˢ Icc (-R) R))
    {C : Set (E × ℝ)} (closedC : IsClosed C)
    (refEstimate : ∀ L ∈ Icc 0 T, ∀ g : ℝ → E, ContinuousOn g (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, g t ∈ closedBall 0 e ∧ (g t,(0:ℝ)) ∈ C) →
      (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (L • B (g t,0)) t) →
      g 0 ∈ A → ‖g 1‖ < e ∧ (L = T → ‖g 1‖ < d)) :
    ∃ η > (0 : ℝ), ∀ L ∈ Icc 0 T, ∀ z : ℝ → E, ∀ r : ℝ → ℝ,
      (∀ t ∈ Icc 0 L, |r t| ≤ η) →
      (∀ t ∈ Icc 0 L, ‖z t‖ ≤ e → (z t,r t) ∈ C) →
      (∀ t ∈ Icc 0 L, HasDerivWithinAt z (B (z t, r t)) (Icc 0 L) t) →
      z 0 ∈ A → (∀ t ∈ Icc 0 L, ‖z t‖ < e) ∧ (L = T → ‖z L‖ < d) := by
  let bad := {x : E × ℝ | e ≤ ‖x.1‖} ∪ {x : E × ℝ | x.2 = T ∧ d ≤ ‖x.1‖}
  have hbad : IsClosed bad := (isClosed_le continuous_const continuous_fst.norm).union
    ((isClosed_eq continuous_snd continuous_const).inter
      (isClosed_le continuous_const continuous_fst.norm))
  obtain ⟨η,hη,test⟩ := robust_stopped_segments (T := T) (isCompact_closedBall 0 e)
    hA hbad hB closedC (by
      intro L hL g hc hq hd h₀
      obtain ⟨he,ht⟩ := refEstimate L hL g hc hq hd h₀
      rintro (hh|⟨hL,hb⟩)
      · exact he.not_ge hh
      · exact (ht hL).not_ge hb)
  refine ⟨min η R, lt_min hη hR, ?_⟩
  intro L hL z r hr hgraph hd hz
  have small t (ht : t ∈ Icc 0 L) := (hr t ht).trans (min_le_left η R)
  have rbound t (ht : t ∈ Icc 0 L) : r t ∈ Icc (-R) R :=
    abs_le.mp ((hr t ht).trans (min_le_right η R))
  have hc : ContinuousOn (fun t => ‖z t‖) (Icc 0 L) :=
    (show ContinuousOn z (Icc 0 L) from fun t ht => (hd t ht).continuousWithinAt).norm
  have confined : ∀ t ∈ Icc 0 L, ‖z t‖ < e := by
    intro t ht
    by_contra! ht'
    obtain ⟨s,hs,es,upto⟩ := first_contact ht.1
      (hc.mono (Icc_subset_Icc_right ht.2)) (start _ hz) ht'
    have sub : Icc 0 s ⊆ Icc 0 L := Icc_subset_Icc_right (hs.2.trans ht.2)
    apply test s ⟨hs.1.le, (hs.2.trans ht.2).trans hL.2⟩ z r
      (fun v hv => small v (sub hv))
      (fun v hv => ⟨⟨by simpa using upto v hv, rbound v (sub hv)⟩, hgraph v (sub hv) (upto v hv)⟩)
      (fun v hv => (hd v (sub hv)).mono sub) hz
    exact Or.inl es.ge
  refine ⟨confined, fun he => ?_⟩
  by_contra! hd'
  apply test L hL z r small (fun v hv =>
    ⟨⟨by simpa using (confined v hv).le, rbound v hv⟩, hgraph v hv (confined v hv).le⟩) hd hz
  exact Or.inr ⟨he,hd'⟩

end CBFIndependence
