import CBFIndependence.Cascade
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Uniform reference estimates from strong LAS

All convergence statements concern every maximal solution.  Compactness is
derived from the continuous ODE and the diagonal Arzelà–Ascoli theorem, not
assumed as a convergence hypothesis.  A closed invariant set may restrict the
initial conditions, as required for stability relative to a boundary manifold.
-/

namespace CBFIndependence

open Set Filter Metric Topology
open scoped NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A closed initial set and a compact trajectory range give sequential
compactness for any ODE family closed under the displayed limiting solutions. -/
theorem solutionFamily_sequentialCompact_of_uniformBound
    {F : E → E} {S : Set (ForwardCurve E)} {A K : Set E}
    (hF : ContinuousOn F K) (hA : IsClosed A) (hK : IsCompact K)
    (hsolves : ∀ c ∈ S, SolvesODE F c)
    (hglobal : ∀ c ∈ S, c.curve 0 ∈ A → c.IsGlobal)
    (hbound : ∀ c ∈ S, c.curve 0 ∈ A → ∀ t, 0 ≤ t → c.curve t ∈ K)
    (hclosed : ∀ d, SolvesODE F d → d.IsGlobal →
      (∀ t, 0 ≤ t → d.curve t ∈ K) → d.curve 0 ∈ A → d ∈ S) :
    SequentialCompactTrajectories S A := by
  intro c hc
  have hcglobal (n : ℕ) := hglobal (c n) (hc n).1 (hc n).2
  have hcinK (n : ℕ) := hbound (c n) (hc n).1 (hc n).2
  have hcderiv (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (c n).curve (F ((c n).curve t)) (Ici 0) t :=
    hsolves (c n) (hc n).1 t ((c n).inDomain_of_global (hcglobal n) ht)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF
  have hlip (n : ℕ) : LipschitzOnWith (Real.toNNReal M) (c n).curve (Ici 0) := by
    apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => hcderiv n t ht)
    intro t ht
    exact_mod_cast (hM _ (hcinK n t ht)).trans (Real.le_coe_toNNReal M)
  obtain ⟨g, φ, hφ, hg⟩ := trajectory_subsequence_locally_uniform hK hcinK hlip
  have hgcont (T : ℝ) (hT : 0 ≤ T) : ContinuousOn g (Icc 0 T) :=
    (hg T hT).continuousOn (.of_forall (fun n =>
      ((hlip (φ n)).mono Icc_subset_Ici_self).continuousOn))
  have hginK (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) : g t ∈ K :=
    hK.isClosed.mem_of_tendsto ((hg T hT).tendsto_at ht)
      (.of_forall (fun n => hcinK (φ n) t ht.1))
  have hdg (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt g (F (g t)) t := by
    have hr : TendstoUniformlyOn (fun (_ : ℕ) (_ : ℝ) => (0 : ℝ))
        (fun _ => 0) atTop (Icc 0 T) := by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact .of_forall (fun _ _ _ => by simpa using hε)
    exact derivative_limit_of_vanishing_normal
      (K := K ×ˢ ({0} : Set ℝ)) (B := fun q : E × ℝ => F q.1)
      (hK.prod isCompact_singleton)
      (hF.comp continuous_fst.continuousOn (fun _ hx => hx.1)) (hg T hT) hr
      (fun n s hs => ⟨hcinK (φ n) s hs.1, rfl⟩)
      (fun n s hs => (hcderiv (φ n) s hs.1.le).hasDerivAt (Ici_mem_nhds hs.1)) ht
  let d : ForwardCurve E := ForwardCurve.global g
  have hdsolve : SolvesODE F d := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    by_cases hz : t = 0
    · subst t
      exact segment_initial_derivative (show (0 : ℝ) < 1 by norm_num)
        (hgcont 1 zero_le_one)
        (hF.comp (hgcont 1 zero_le_one) (fun t ht => hginK 1 zero_le_one t ht))
        (fun s hs => hdg 1 zero_le_one s hs)
    · exact (hdg (t + 1) (by linarith) t
        ⟨lt_of_le_of_ne ht0 (Ne.symm hz), by linarith⟩).hasDerivWithinAt
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n => (c (φ n)).curve t) atTop (𝓝 (d.curve t)) :=
    (hg t ht).tendsto_at (right_mem_Icc.mpr ht)
  have hdA : d.curve 0 ∈ A :=
    hA.mem_of_tendsto (hpoint 0 le_rfl) (.of_forall (fun n => (hc (φ n)).2))
  have hdmem : d ∈ S := hclosed d hdsolve rfl
    (fun t ht => hginK t ht t (right_mem_Icc.mpr ht)) hdA
  exact ⟨φ, hφ, d, hdmem, hdA, hpoint⟩

theorem maximalSolutionsFromOn_sequentialCompact
    {F : E → E} {U Bdy A K : Set E}
    (hF : ContinuousOn F K) (hA : IsClosed A) (hK : IsCompact K)
    (hKU : K ⊆ U) (hABdy : A ⊆ Bdy)
    (hglobal : ∀ c ∈ MaximalSolutionsFromOn F U Bdy,
      c.curve 0 ∈ A → c.IsGlobal)
    (hbound : ∀ c ∈ MaximalSolutionsFromOn F U Bdy,
      c.curve 0 ∈ A → ∀ t, 0 ≤ t → c.curve t ∈ K) :
    SequentialCompactTrajectories (MaximalSolutionsFromOn F U Bdy) A := by
  apply solutionFamily_sequentialCompact_of_uniformBound hF hA hK
    (fun c hc => hc.1.1.1) hglobal hbound
  intro d hd hg hrange hinit
  exact ⟨global_solutionOn_maximal ⟨hd,
    fun t ht => hKU (hrange t ht.1)⟩ hg, hABdy hinit⟩

/-- Relative initial-condition families are restart-closed when Bdy is invariant
along their complete solutions. -/
theorem maximalSolutionsFromOn_globalShiftClosed
    {F : E → E} {U Bdy : Set E}
    (hinvariant : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.IsGlobal →
      ∀ t, 0 ≤ t → c.curve t ∈ Bdy) :
    GlobalShiftClosed (MaximalSolutionsFromOn F U Bdy) := by
  intro c hc hg s hs
  refine ⟨maximalSolutionsOn_globalShiftClosed F U c hc.1 hg s hs, ?_⟩
  simpa [globalShift, ForwardCurve.global] using hinvariant c hc hg s hs

/-- Uniform attraction on a fixed closed initial set follows from all-solution
attraction, strong stability, compact confinement, and invariance. -/
theorem uniform_attraction_on_relative_initial_set
    {F : E → E} {U Bdy A K : Set E} {p : E}
    (hF : ContinuousOn F K) (hA : IsClosed A) (hK : IsCompact K)
    (hKU : K ⊆ U) (hABdy : A ⊆ Bdy)
    (hs : StrongStable (MaximalSolutionsFromOn F U Bdy) p)
    (hinvariant : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.IsGlobal →
      ∀ t, 0 ≤ t → c.curve t ∈ Bdy)
    (ha : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.curve 0 ∈ A →
      c.IsGlobal ∧ Tendsto c.curve atTop (𝓝 p))
    (hbound : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K) :
    ∀ ε > 0, ∃ T, 0 ≤ T ∧
      ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.curve 0 ∈ A →
        ∀ t, T ≤ t → dist (c.curve t) p < ε := by
  exact uniform_attraction_of_compact_trajectories hs
    (maximalSolutionsFromOn_globalShiftClosed hinvariant)
    (maximalSolutionsFromOn_sequentialCompact hF hA hK hKU hABdy
      (fun c hc hinit => (ha c hc hinit).1) hbound) ha

/-- The reference estimates needed by finite-time robustness are consequences
of raw relative strong LAS.  In particular, a common attraction time is not an
extra hypothesis.  Every nearby reference solution remains within half the
prescribed outer radius, leaving a positive perturbation margin. -/
theorem strongLAS_relative_uniform_reference
    [FiniteDimensional ℝ E]
    {F : E → E} {U Bdy : Set E} {p : E} {R : ℝ}
    (hF : ContinuousOn F U) (hBdy : IsClosed Bdy)
    (hR : 0 < R) (hRU : closedBall p R ⊆ U)
    (hinvariant : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.IsGlobal →
      ∀ t, 0 ≤ t → c.curve t ∈ Bdy)
    (hLAS : StrongLAS (MaximalSolutionsFromOn F U Bdy) p) :
    ∃ r > 0, r < R / 2 ∧
      (∀ c ∈ MaximalSolutionsFromOn F U Bdy, dist (c.curve 0) p ≤ r →
        c.IsGlobal ∧ ∀ t, 0 ≤ t → dist (c.curve t) p < R / 2) ∧
      ∀ ε > 0, ∃ T, 0 ≤ T ∧
        ∀ c ∈ MaximalSolutionsFromOn F U Bdy, dist (c.curve 0) p ≤ r →
          ∀ t, T ≤ t → dist (c.curve t) p < ε := by
  obtain ⟨δs, hδs, hstable⟩ := hLAS.1 (R / 2) (half_pos hR)
  obtain ⟨δa, hδa, hattract⟩ := hLAS.2
  let r : ℝ := min δs (min δa (R / 2)) / 2
  have hr : 0 < r := half_pos (lt_min hδs (lt_min hδa (half_pos hR)))
  have hrmin : r < min δs (min δa (R / 2)) :=
    half_lt_self (lt_min hδs (lt_min hδa (half_pos hR)))
  have hrs : r < δs := hrmin.trans_le (min_le_left _ _)
  have hra : r < δa := hrmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrR : r < R / 2 := hrmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let A := closedBall p r ∩ Bdy
  let K := closedBall p (R / 2)
  have hAclosed : IsClosed A := isClosed_closedBall.inter hBdy
  have hKcompact : IsCompact K := isCompact_closedBall p (R / 2)
  have hKU : K ⊆ U :=
    (closedBall_subset_closedBall (half_le_self hR.le)).trans hRU
  have hABdy : A ⊆ Bdy := inter_subset_right
  have ha : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.curve 0 ∈ A →
      c.IsGlobal ∧ Tendsto c.curve atTop (𝓝 p) := by
    intro c hc hinit
    exact hattract c hc ((show dist (c.curve 0) p ≤ r from hinit.1).trans_lt hra)
  have hbound : ∀ c ∈ MaximalSolutionsFromOn F U Bdy, c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K := by
    intro c hc hinit t ht
    have hg := (ha c hc hinit).1
    exact (hstable c hc
      ((show dist (c.curve 0) p ≤ r from hinit.1).trans_lt hrs)
      t (c.inDomain_of_global hg ht)).le
  have huniform := uniform_attraction_on_relative_initial_set
    (hF.mono hKU) hAclosed hKcompact hKU hABdy hLAS.1 hinvariant ha hbound
  refine ⟨r, hr, hrR, ?_, ?_⟩
  · intro c hc hinit
    have hg := (hattract c hc (hinit.trans_lt hra)).1
    exact ⟨hg, fun t ht => hstable c hc (hinit.trans_lt hrs)
      t (c.inDomain_of_global hg ht)⟩
  · intro ε hε
    obtain ⟨T, hT, htail⟩ := huniform ε hε
    exact ⟨T, hT, fun c hc hinit => htail c hc ⟨hinit, hc.2⟩⟩


/-- Sequential compactness for maximal solutions on a state domain, with the
compact trajectory range contained in that domain. -/
theorem maximalSolutionsOn_sequentialCompact_in_domain
    {F : E → E} {U A K : Set E}
    (hF : ContinuousOn F K) (hA : IsClosed A) (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hglobal : ∀ c ∈ MaximalSolutionsOn F U, c.curve 0 ∈ A → c.IsGlobal)
    (hbound : ∀ c ∈ MaximalSolutionsOn F U, c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K) :
    SequentialCompactTrajectories (MaximalSolutionsOn F U) A := by
  apply solutionFamily_sequentialCompact_of_uniformBound hF hA hK
    (fun c hc => hc.1.1) hglobal hbound
  intro d hd hg hrange _
  exact global_solutionOn_maximal ⟨hd,
    fun t ht => hKU (hrange t ht.1)⟩ hg

/-- Centered reference estimates in exactly the form used by the boundary
reduction. The state domain is V intersect Bdy, and continuity is needed only on
that domain. The compact range is intersected with Bdy, so no neighborhood of
zero inside the boundary manifold is mistakenly required to contain a ball. -/
theorem strongLAS_on_inter_uniform_reference
    [FiniteDimensional ℝ E]
    {F : E → E} {V Bdy : Set E} {Rbar : ℝ}
    (hBdy : IsClosed Bdy) (hF : ContinuousOn F (V ∩ Bdy))
    (hV : ball (0 : E) Rbar ⊆ V)
    (hLAS : StrongLAS (MaximalSolutionsOn F (V ∩ Bdy)) 0) :
    ∀ e > 0, e ≤ Rbar → ∃ a > 0, a < e ∧
      ∀ d > 0, ∃ T > 0,
        ∀ c ∈ MaximalSolutionsOn F (V ∩ Bdy),
          c.curve 0 ∈ closedBall (0 : E) a →
          c.IsGlobal ∧
          (∀ t, 0 ≤ t → ‖c.curve t‖ < e) ∧ ‖c.curve T‖ < d := by
  intro e he heR
  obtain ⟨δs, hδs, hstable⟩ := hLAS.1 (e / 2) (half_pos he)
  obtain ⟨δa, hδa, hattract⟩ := hLAS.2
  let a : ℝ := min δs (min δa e) / 2
  have ha : 0 < a := half_pos (lt_min hδs (lt_min hδa he))
  have hamin : a < min δs (min δa e) :=
    half_lt_self (lt_min hδs (lt_min hδa he))
  have has : a < δs := hamin.trans_le (min_le_left _ _)
  have haa : a < δa := hamin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < e := hamin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let A := closedBall (0 : E) a ∩ Bdy
  let K := closedBall (0 : E) (e / 2) ∩ Bdy
  have hAclosed : IsClosed A := isClosed_closedBall.inter hBdy
  have hKcompact : IsCompact K := (isCompact_closedBall (0 : E) (e / 2)).inter_right hBdy
  have hKU : K ⊆ V ∩ Bdy := by
    intro x hx
    refine ⟨hV ?_, hx.2⟩
    change dist x 0 < Rbar
    exact (show dist x 0 ≤ e / 2 from hx.1).trans_lt
      ((half_lt_self he).trans_le heR)
  have hattr : ∀ c ∈ MaximalSolutionsOn F (V ∩ Bdy), c.curve 0 ∈ A →
      c.IsGlobal ∧ Tendsto c.curve atTop (𝓝 (0 : E)) := by
    intro c hc hinit
    exact hattract c hc ((show dist (c.curve 0) 0 ≤ a from hinit.1).trans_lt haa)
  have hbound : ∀ c ∈ MaximalSolutionsOn F (V ∩ Bdy), c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K := by
    intro c hc hinit t ht
    have hdom := c.inDomain_of_global (hattr c hc hinit).1 ht
    exact ⟨(hstable c hc
      ((show dist (c.curve 0) 0 ≤ a from hinit.1).trans_lt has) t hdom).le,
      (hc.1.2 t hdom).2⟩
  have hcomp := maximalSolutionsOn_sequentialCompact_in_domain
    (hF.mono hKU) hAclosed hKcompact hKU
    (fun c hc hinit => (hattr c hc hinit).1) hbound
  have huniform := uniform_attraction_of_compact_trajectories hLAS.1
    (maximalSolutionsOn_globalShiftClosed F (V ∩ Bdy)) hcomp hattr
  refine ⟨a, ha, hae, ?_⟩
  intro d hd
  obtain ⟨T, hT, htail⟩ := huniform d hd
  refine ⟨T + 1, by linarith, ?_⟩
  intro c hc hinit
  have hinitA : c.curve 0 ∈ A := ⟨hinit, (hc.1.2 0 c.zero_inDomain).2⟩
  have hg := (hattr c hc hinitA).1
  refine ⟨hg, ?_, ?_⟩
  · intro t ht
    have hsmall := hstable c hc
      ((show dist (c.curve 0) 0 ≤ a from hinit).trans_lt has)
      t (c.inDomain_of_global hg ht)
    simpa only [dist_zero_right] using hsmall.trans (half_lt_self he)
  · simpa only [dist_zero_right] using htail c hc hinitA (T + 1) (by linarith)

end CBFIndependence

