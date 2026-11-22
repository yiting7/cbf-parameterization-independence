import CBFIndependence.Statement
import CBFIndependence.Diagonal
import CBFIndependence.TimeBlocks
import CBFIndependence.Scalar
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic

/-!
# Trajectories and strong local asymptotic stability

Every forward trajectory carries its lifetime. Attraction requires all nearby
maximal trajectories to exist for all positive time and converge. The finite
time estimates below apply before forward completeness has been established.
-/

namespace CBFIndependence

open Set Filter Metric
open scoped Topology ENNReal

namespace ForwardCurve
variable {E F : Type*}

def map (f : E → F) (c : ForwardCurve E) : ForwardCurve F where
  curve := f ∘ c.curve
  lifetime := c.lifetime
  positive_lifetime := c.positive_lifetime

def global (γ : ℝ → E) : ForwardCurve E where
  curve := γ
  lifetime := ⊤
  positive_lifetime := by simp

@[simp] theorem zero_inDomain (c : ForwardCurve E) : c.InDomain 0 := by
  exact ⟨le_rfl, by simpa using c.positive_lifetime⟩

@[simp] theorem map_inDomain (f : E → F) (c : ForwardCurve E) (t : ℝ) :
    (c.map f).InDomain t ↔ c.InDomain t := Iff.rfl

@[simp] theorem map_isGlobal (f : E → F) (c : ForwardCurve E) :
    (c.map f).IsGlobal ↔ c.IsGlobal := Iff.rfl

@[simp] theorem global_inDomain (γ : ℝ → E) (t : ℝ) :
    (global γ).InDomain t ↔ 0 ≤ t := by
  simp [InDomain, global]

theorem inDomain_of_global (c : ForwardCurve E) (h : c.IsGlobal)
    {t : ℝ} (ht : 0 ≤ t) : c.InDomain t := by
  exact ⟨ht, by simpa [IsGlobal] using (show ENNReal.ofReal t < c.lifetime by
    rw [h]
    exact ENNReal.ofReal_lt_top)⟩

theorem inDomain_mono (c : ForwardCurve E) {s t : ℝ}
    (ht : c.InDomain t) (hs : 0 ≤ s) (hst : s ≤ t) : c.InDomain s :=
  ⟨hs, (ENNReal.ofReal_le_ofReal hst).trans_lt ht.2⟩

theorem extends_refl (c : ForwardCurve E) : c.Extends c :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem extends_trans {a b c : ForwardCurve E}
    (hab : a.Extends b) (hbc : b.Extends c) : a.Extends c := by
  refine ⟨hbc.1.trans hab.1, ?_⟩
  intro t ht
  exact (hab.2 t ⟨ht.1, ht.2.trans_le hbc.1⟩).trans (hbc.2 t ht)

end ForwardCurve

section ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A solution is maximal if every solution extending it has the same lifetime. -/
def MaximalSolution (F : E → E) (c : ForwardCurve E) : Prop :=
  SolvesODE F c ∧ ∀ d, SolvesODE F d → d.Extends c → d.lifetime = c.lifetime

def MaximalSolutions (F : E → E) : Set (ForwardCurve E) :=
  {c | MaximalSolution F c}

theorem global_solution_maximal {F : E → E} {c : ForwardCurve E}
    (hs : SolvesODE F c) (hg : c.IsGlobal) : MaximalSolution F c := by
  refine ⟨hs, ?_⟩
  intro d _ hd
  have htop : d.lifetime = ⊤ := top_le_iff.mp (hg ▸ hd.1)
  exact htop.trans hg.symm

theorem global_solutionOn_maximal {F : E → E} {U : Set E} {c : ForwardCurve E}
    (hs : SolvesODEOn F U c) (hg : c.IsGlobal) : MaximalSolutionOn F U c := by
  refine ⟨hs, ?_⟩
  intro d _ hd
  have htop : d.lifetime = ⊤ := top_le_iff.mp (hg ▸ hd.1)
  exact htop.trans hg.symm

end ODE

section Stability

variable {E : Type*} [PseudoMetricSpace E]

theorem StrongStable.mono {S T : Set (ForwardCurve E)} {p : E}
    (h : StrongStable T p) (hST : S ⊆ T) : StrongStable S p := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  exact ⟨δ, hδ, fun c hc => h c (hST hc)⟩

theorem StrongAttractive.mono {S T : Set (ForwardCurve E)} {p : E}
    (h : StrongAttractive T p) (hST : S ⊆ T) : StrongAttractive S p := by
  obtain ⟨δ, hδ, h⟩ := h
  exact ⟨δ, hδ, fun c hc => h c (hST hc)⟩

theorem StrongLAS.mono {S T : Set (ForwardCurve E)} {p : E}
    (h : StrongLAS T p) (hST : S ⊆ T) : StrongLAS S p :=
  ⟨h.1.mono hST, h.2.mono hST⟩

end Stability

section BoundaryRestriction

variable {E : Type*} [PseudoMetricSpace E]

/-- Embed a boundary curve as a curve whose scalar normal coordinate is zero. -/
def boundaryLift (c : ForwardCurve E) : ForwardCurve (E × ℝ) :=
  c.map (fun z => (z, 0))

def BoundaryRestriction (S : Set (ForwardCurve (E × ℝ))) : Set (ForwardCurve E) :=
  {c | boundaryLift c ∈ S}

theorem strongStable_boundary_of_full {S : Set (ForwardCurve (E × ℝ))} {p : E}
    (h : StrongStable S (p, 0)) : StrongStable (BoundaryRestriction S) p := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  refine ⟨δ, hδ, ?_⟩
  intro c hc hinit t ht
  have hinit' : dist ((boundaryLift c).curve 0) (p, 0) < δ := by
    simpa [boundaryLift, ForwardCurve.map] using hinit
  have ht' : (boundaryLift c).InDomain t := ht
  simpa [boundaryLift, ForwardCurve.map] using h (boundaryLift c) hc hinit' t ht'

theorem strongAttractive_boundary_of_full {S : Set (ForwardCurve (E × ℝ))} {p : E}
    (h : StrongAttractive S (p, 0)) : StrongAttractive (BoundaryRestriction S) p := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, ?_⟩
  intro c hc hinit
  have hinit' : dist ((boundaryLift c).curve 0) (p, 0) < δ := by
    simpa [boundaryLift, ForwardCurve.map] using hinit
  obtain ⟨hg, hl⟩ := h (boundaryLift c) hc hinit'
  refine ⟨hg, ?_⟩
  simpa [boundaryLift, ForwardCurve.map, Function.comp_def] using
    (continuous_fst.tendsto (p, (0 : ℝ))).comp hl

/-- The restriction/necessity direction is valid for nonunique solution families
and keeps the completeness requirement rather than discarding finite lifetimes. -/
theorem strongLAS_boundary_of_full {S : Set (ForwardCurve (E × ℝ))} {p : E}
    (h : StrongLAS S (p, 0)) : StrongLAS (BoundaryRestriction S) p :=
  ⟨strongStable_boundary_of_full h.1, strongAttractive_boundary_of_full h.2⟩

end BoundaryRestriction

section BoundaryODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def cascadeField (b : E → ℝ → E) (α : ℝ → ℝ) (x : E × ℝ) : E × ℝ :=
  (b x.1 x.2, -α x.2)

/-- Every boundary solution lifts to a solution of the cascade. This is a
derivative calculation, not an assumption of a boundary dynamics theorem. -/
theorem boundary_solution_lifts {b : E → ℝ → E} {α : ℝ → ℝ}
    (hα : α 0 = 0) {c : ForwardCurve E}
    (hc : SolvesODE (fun z => b z 0) c) :
    SolvesODE (cascadeField b α) (boundaryLift c) := by
  intro t ht
  have hz := hc t ht
  have hr := hasDerivWithinAt_const t (Ici (0 : ℝ)) (0 : ℝ)
  simpa [boundaryLift, ForwardCurve.map, cascadeField, hα, Function.comp_def]
    using hz.prodMk hr

end BoundaryODE

section Trapping

variable {E : Type*} [PseudoMetricSpace E]

/-- The purely deterministic iteration step in the cascade argument. A local
inward return at the end of each fixed time block implies trapping for all
times. Neither uniqueness nor a semigroup/flow is used. -/
theorem fixed_time_return_traps (x : ℝ → E) (p : E) {T a ε : ℝ}
    (hT : 0 < T) (hinit : dist (x 0) p ≤ a)
    (hstep : ∀ s, 0 ≤ s → dist (x s) p ≤ a →
      (∀ τ ∈ Icc 0 T, dist (x (s + τ)) p < ε) ∧
      dist (x (s + T)) p ≤ a) :
    ∀ t, 0 ≤ t → dist (x t) p < ε := by
  have hgrid : ∀ n : ℕ, dist (x ((n : ℝ) * T)) p ≤ a := by
    intro n
    induction n with
    | zero => simpa using hinit
    | succ n ih =>
      have h := (hstep ((n : ℝ) * T)
        (mul_nonneg (Nat.cast_nonneg _) hT.le) ih).2
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using h
  intro t ht
  let n : ℕ := ⌊t / T⌋₊
  have hlow : (n : ℝ) * T ≤ t := by
    have hf : (n : ℝ) ≤ t / T := Nat.floor_le (div_nonneg ht hT.le)
    exact (le_div_iff₀ hT).mp hf
  have hhigh : t < ((n : ℝ) + 1) * T := by
    have hf : t / T < (n : ℝ) + 1 := Nat.lt_floor_add_one (t / T)
    exact (div_lt_iff₀ hT).mp hf
  have hτ : t - (n : ℝ) * T ∈ Icc 0 T := by
    constructor
    · linarith
    · nlinarith
  have h := (hstep ((n : ℝ) * T)
    (mul_nonneg (Nat.cast_nonneg _) hT.le) (hgrid n)).1
    (t - (n : ℝ) * T) hτ
  simpa using h

/-- The lifetime-aware version of fixed-time trapping. Only blocks contained
in the original trajectory's domain are used, so forward completeness is not
assumed in order to prove the bound needed for continuation. -/
theorem finite_lifetime_return_traps (c : ForwardCurve E) (p : E) {T a ε : ℝ}
    (hT : 0 < T) (hinit : dist (c.curve 0) p ≤ a)
    (hstep : ∀ s, c.InDomain s → dist (c.curve s) p ≤ a →
      ∀ L ∈ Icc 0 T, c.InDomain (s + L) →
        dist (c.curve (s + L)) p < ε ∧
        (L = T → dist (c.curve (s + L)) p ≤ a)) :
    ∀ t, c.InDomain t → dist (c.curve t) p < ε := by
  have hgrid : ∀ n : ℕ, c.InDomain ((n : ℝ) * T) →
      dist (c.curve ((n : ℝ) * T)) p ≤ a := by
    intro n
    induction n with
    | zero => intro _; simpa using hinit
    | succ n ih =>
      intro hdom
      have heq : ((n + 1 : ℕ) : ℝ) * T = (n : ℝ) * T + T := by push_cast; ring
      have hdom' : c.InDomain ((n : ℝ) * T + T) := heq ▸ hdom
      have hprev : c.InDomain ((n : ℝ) * T) :=
        c.inDomain_mono hdom' (mul_nonneg (Nat.cast_nonneg _) hT.le) (by linarith)
      have h := (hstep ((n : ℝ) * T) hprev (ih hprev) T ⟨hT.le, le_rfl⟩ hdom').2 rfl
      simpa [Nat.cast_add, Nat.cast_one, add_mul] using h
  intro t ht
  let n : ℕ := ⌊t / T⌋₊
  have hlow : (n : ℝ) * T ≤ t :=
    (le_div_iff₀ hT).mp (Nat.floor_le (div_nonneg ht.1 hT.le))
  have hhigh : t < ((n : ℝ) + 1) * T :=
    (div_lt_iff₀ hT).mp (Nat.lt_floor_add_one (t / T))
  have hn : c.InDomain ((n : ℝ) * T) :=
    c.inDomain_mono ht (mul_nonneg (Nat.cast_nonneg _) hT.le) hlow
  have hL : t - (n : ℝ) * T ∈ Icc 0 T := by constructor <;> nlinarith
  have hend : c.InDomain ((n : ℝ) * T + (t - (n : ℝ) * T)) := by simpa using ht
  simpa using (hstep ((n : ℝ) * T) hn (hgrid n hn)
    (t - (n : ℝ) * T) hL hend).1

/-- Future stability along one trajectory, uniform in the restart time. -/
def FutureStable (x : ℝ → E) (p : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ s, 0 ≤ s → dist (x s) p < δ →
    ∀ t, s ≤ t → dist (x t) p < ε

/-- The final attraction step: entering every small neighborhood plus future
stability gives convergence. The entries need not have uniform entry times. -/
theorem tendsto_of_futureStable_of_enters {x : ℝ → E} {p : E}
    (hstable : FutureStable x p)
    (henter : ∀ δ > 0, ∃ s, 0 ≤ s ∧ dist (x s) p < δ) :
    Tendsto x atTop (𝓝 p) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := hstable ε hε
  obtain ⟨s, hs0, hsd⟩ := henter δ hδ
  exact ⟨s, fun t ht => hs s hs0 hsd t ht⟩

def globalShift (c : ForwardCurve E) (s : ℝ) : ForwardCurve E :=
  ForwardCurve.global (fun t => c.curve (t + s))

/-- Autonomous solution families are closed under restarting a complete
solution at a nonnegative time. -/
def GlobalShiftClosed (S : Set (ForwardCurve E)) : Prop :=
  ∀ c ∈ S, c.IsGlobal → ∀ s, 0 ≤ s → globalShift c s ∈ S

theorem StrongStable.futureStable {S : Set (ForwardCurve E)} {p : E}
    (hs : StrongStable S p) (hshift : GlobalShiftClosed S)
    {c : ForwardCurve E} (hc : c ∈ S) (hg : c.IsGlobal) :
    FutureStable c.curve p := by
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hs ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs0 hsd t hst
  have hmem := hshift c hc hg s hs0
  have hinit : dist ((globalShift c s).curve 0) p < δ := by
    simpa [globalShift, ForwardCurve.global] using hsd
  have ht : (globalShift c s).InDomain (t - s) := by
    simpa [globalShift] using sub_nonneg.mpr hst
  simpa [globalShift, ForwardCurve.global] using hd (globalShift c s) hmem hinit
    (t - s) ht

end Trapping

section AutonomousRestart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem solvesODE_globalShift {F : E → E} {c : ForwardCurve E}
    (hc : SolvesODE F c) (hg : c.IsGlobal) {s : ℝ} (hs : 0 ≤ s) :
    SolvesODE F (globalShift c s) := by
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have hdom := c.inDomain_of_global hg (add_nonneg ht0 hs)
  have hd := hc (t + s) hdom
  have harg : HasDerivWithinAt (fun u : ℝ => u + s) 1 (Ici 0) t :=
    ((hasDerivAt_id t).add_const s).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => u + s) (Ici 0) (Ici 0) :=
    fun u hu => add_nonneg hu hs
  simpa [globalShift, ForwardCurve.global, Function.comp_def] using hd.scomp t harg hmaps

theorem maximalSolutions_globalShiftClosed (F : E → E) :
    GlobalShiftClosed (MaximalSolutions F) := by
  intro c hc hg s hs
  exact global_solution_maximal (solvesODE_globalShift hc.1 hg hs) rfl

theorem maximalSolutionsOn_globalShiftClosed (F : E → E) (U : Set E) :
    GlobalShiftClosed (MaximalSolutionsOn F U) := by
  intro c hc hg s hs
  apply global_solutionOn_maximal (c := globalShift c s) _ rfl
  refine ⟨solvesODE_globalShift hc.1.1 hg hs, ?_⟩
  intro t ht
  exact hc.1.2 (t + s) (c.inDomain_of_global hg (add_nonneg ht.1 hs))

end AutonomousRestart

section CompactAttraction

variable {E : Type*} [PseudoMetricSpace E]

/-- The specific compactness interface used to turn all-solution attractivity
into uniform attractivity on a compact initial set. This is a compactness
property, not a stability or convergence assumption. It must be established
from the ODE before applying the theorem below. -/
def SequentialCompactTrajectories (S : Set (ForwardCurve E)) (K : Set E) : Prop :=
  ∀ c : ℕ → ForwardCurve E,
    (∀ n, c n ∈ S ∧ (c n).curve 0 ∈ K) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ d ∈ S, d.curve 0 ∈ K ∧
        ∀ t, 0 ≤ t →
          Tendsto (fun n => (c (φ n)).curve t) atTop (𝓝 (d.curve t))

/-- Strong attractivity is uniform on a solution-compact initial set, provided
all solutions remain in the family after time shifts. This argument permits
nonunique solutions throughout. -/
theorem uniform_attraction_of_compact_trajectories
    {S : Set (ForwardCurve E)} {K : Set E} {p : E}
    (hs : StrongStable S p) (hshift : GlobalShiftClosed S)
    (hcompact : SequentialCompactTrajectories S K)
    (ha : ∀ c ∈ S, c.curve 0 ∈ K →
      c.IsGlobal ∧ Tendsto c.curve atTop (𝓝 p)) :
    ∀ ε > 0, ∃ T, 0 ≤ T ∧
      ∀ c ∈ S, c.curve 0 ∈ K → ∀ t, T ≤ t → dist (c.curve t) p < ε := by
  intro ε hε
  by_contra h
  push_neg at h
  have hn : ∀ n : ℕ, ∃ c ∈ S, c.curve 0 ∈ K ∧
      ∃ t : ℝ, (n : ℝ) ≤ t ∧ ε ≤ dist (c.curve t) p := by
    intro n
    obtain ⟨c, hc, hK, t, ht, hd⟩ := h (n : ℝ) (Nat.cast_nonneg n)
    exact ⟨c, hc, hK, t, ht, hd⟩
  choose c hc hK t ht hd using hn
  obtain ⟨φ, hφ, d, hdS, hdK, hlim⟩ := hcompact c (fun n => ⟨hc n, hK n⟩)
  obtain ⟨δ, hδ, hstable⟩ := hs ε hε
  obtain ⟨T, hT⟩ := Metric.tendsto_atTop.mp (ha d hdS hdK).2
    (δ / 2) (half_pos hδ)
  let T₀ : ℝ := max T 0
  have hT₀ : 0 ≤ T₀ := le_max_right _ _
  have hdsmall : dist (d.curve T₀) p < δ :=
    (hT T₀ (le_max_left _ _)).trans (half_lt_self hδ)
  have hev : ∀ᶠ n : ℕ in atTop, dist ((c (φ n)).curve T₀) p < δ :=
    ((hlim T₀ hT₀).dist (tendsto_const_nhds (x := p))).eventually_lt_const hdsmall
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨M, hM⟩ := exists_nat_ge T₀
  let n : ℕ := max N M
  have hNn : N ≤ n := le_max_left _ _
  have hMn : M ≤ n := le_max_right _ _
  have hφn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
  have hlate : T₀ ≤ t (φ n) :=
    hM.trans ((Nat.cast_le.mpr hMn).trans (hφn.trans (ht (φ n))))
  have hmem : globalShift (c (φ n)) T₀ ∈ S :=
    hshift (c (φ n)) (hc (φ n)) (ha (c (φ n)) (hc (φ n)) (hK (φ n))).1
      T₀ hT₀
  have hinit : dist ((globalShift (c (φ n)) T₀).curve 0) p < δ := by
    simpa [globalShift, ForwardCurve.global] using hN n hNn
  have hdom : (globalShift (c (φ n)) T₀).InDomain (t (φ n) - T₀) := by
    simpa [globalShift] using sub_nonneg.mpr hlate
  have hsmall := hstable (globalShift (c (φ n)) T₀) hmem hinit
    (t (φ n) - T₀) hdom
  have hsmall' : dist ((c (φ n)).curve (t (φ n))) p < ε := by
    simpa [globalShift, ForwardCurve.global] using hsmall
  exact (not_lt_of_ge (hd (φ n))) hsmall'

end CompactAttraction

section CompactODETrajectories

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a continuous ODE, complete trajectories with values in one compact set
have the sequential compactness used above. The derivative bound, diagonal
Arzelà–Ascoli extraction, ODE limit, and derivative at time zero are all proved;
no uniqueness or local Lipschitz assumption occurs. -/
theorem maximalSolutions_sequentialCompact_of_uniformBound_on
    {F : E → E} {A K : Set E} (hF : ContinuousOn F K)
    (hA : IsClosed A) (hK : IsCompact K)
    (hglobal : ∀ c ∈ MaximalSolutions F, c.curve 0 ∈ A → c.IsGlobal)
    (hbound : ∀ c ∈ MaximalSolutions F, c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K) :
    SequentialCompactTrajectories (MaximalSolutions F) A := by
  intro c hc
  have hcglobal (n : ℕ) := hglobal (c n) (hc n).1 (hc n).2
  have hcinK (n : ℕ) := hbound (c n) (hc n).1 (hc n).2
  have hcderiv (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (c n).curve (F ((c n).curve t)) (Ici 0) t :=
    (hc n).1.1 t ((c n).inDomain_of_global (hcglobal n) ht)
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
  have hdmem : d ∈ MaximalSolutions F := global_solution_maximal hdsolve rfl
  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      Tendsto (fun n => (c (φ n)).curve t) atTop (𝓝 (d.curve t)) :=
    (hg t ht).tendsto_at (right_mem_Icc.mpr ht)
  have hdA : d.curve 0 ∈ A :=
    hA.mem_of_tendsto (hpoint 0 le_rfl) (.of_forall (fun n => (hc (φ n)).2))
  exact ⟨φ, hφ, d, hdmem, hdA, hpoint⟩

theorem maximalSolutions_sequentialCompact_of_uniformBound
    {F : E → E} (hF : Continuous F) {A K : Set E}
    (hA : IsClosed A) (hK : IsCompact K)
    (hglobal : ∀ c ∈ MaximalSolutions F, c.curve 0 ∈ A → c.IsGlobal)
    (hbound : ∀ c ∈ MaximalSolutions F, c.curve 0 ∈ A →
      ∀ t, 0 ≤ t → c.curve t ∈ K) :
    SequentialCompactTrajectories (MaximalSolutions F) A :=
  maximalSolutions_sequentialCompact_of_uniformBound_on hF.continuousOn hA hK hglobal hbound

end CompactODETrajectories

section CascadeAssembly

variable {E : Type*} [NormedAddCommGroup E]

/-- The scalar coordinate does not increase in norm before the end of any
trajectory's lifetime. See `normalBounds_of_local_equation`. -/
def NormalBound (S : Set (ForwardCurve (E × ℝ))) : Prop :=
  ∀ c ∈ S, ∀ t, c.InDomain t → ‖(c.curve t).2‖ ≤ ‖(c.curve 0).2‖

/-- The precise finite-block estimate used by the trapping proof. The final
time is allowed to be shorter than the return time, avoiding any assumption
of forward completeness in advance. -/
def RestartBlock (S : Set (ForwardCurve (E × ℝ))) (ε a ρ T : ℝ) : Prop :=
  ∀ c ∈ S, ∀ s, c.InDomain s → ‖(c.curve s).1‖ ≤ a →
    ∀ L ∈ Icc 0 T, c.InDomain (s + L) →
      (∀ t ∈ Icc s (s + L), ‖(c.curve t).2‖ ≤ ρ) →
      ‖(c.curve (s + L)).1‖ < ε ∧
      (L = T → ‖(c.curve (s + L)).1‖ ≤ a)

def TangentBlockProperty (S : Set (ForwardCurve (E × ℝ))) : Prop :=
  ∀ ε > 0, ∃ a > 0, ∃ ρ > 0, ∃ T > 0, RestartBlock S ε a ρ T

/-- A local continuation conclusion inside one fixed compact neighborhood. -/
def BoundedContinuation (S : Set (ForwardCurve (E × ℝ))) (R : ℝ) : Prop :=
  ∀ c ∈ S, (∀ t, c.InDomain t → ‖c.curve t‖ ≤ R) → c.IsGlobal

def NormalConvergence (S : Set (ForwardCurve (E × ℝ))) : Prop :=
  ∀ c ∈ S, c.IsGlobal → Tendsto (fun t => (c.curve t).2) atTop (𝓝 0)

/-- The complete-block endpoint estimate used only after trapping and
continuation have been established. -/
def TangentEndpointProperty (S : Set (ForwardCurve (E × ℝ))) (R : ℝ) : Prop :=
  ∀ d > 0, ∃ ρ > 0, ∃ T > 0,
    ∀ c ∈ S, c.IsGlobal → ∀ s, 0 ≤ s →
      (∀ t, s ≤ t → ‖c.curve t‖ ≤ R) →
      (∀ t, s ≤ t → ‖(c.curve t).2‖ ≤ ρ) →
      ‖(c.curve (s + T)).1‖ < d

theorem strongStable_of_finite_blocks
    {S : Set (ForwardCurve (E × ℝ))}
    (hnormal : NormalBound S) (hblocks : TangentBlockProperty S) :
    StrongStable S 0 := by
  intro ε hε
  obtain ⟨a, ha, ρ, hρ, T, hT, hb⟩ := hblocks (ε / 2) (half_pos hε)
  let δ := min a (min ρ (ε / 2))
  have hδ : 0 < δ := lt_min ha (lt_min hρ (half_pos hε))
  refine ⟨δ, hδ, ?_⟩
  intro c hc hinit t ht
  have hi : ‖c.curve 0‖ < δ := by simpa using hinit
  have hza : ‖(c.curve 0).1‖ ≤ a :=
    (norm_fst_le _).trans (hi.le.trans (min_le_left _ _))
  have hrρ : ∀ u, c.InDomain u → ‖(c.curve u).2‖ ≤ ρ := by
    intro u hu
    exact (hnormal c hc u hu).trans ((norm_snd_le _).trans
      (hi.le.trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hz := finite_lifetime_return_traps (c.map Prod.fst) (0 : E) hT
    (by simpa [ForwardCurve.map] using hza) (by
      intro s hs hsa L hL hend
      have hsa' : ‖(c.curve s).1‖ ≤ a := by simpa [ForwardCurve.map] using hsa
      have hnorm : ∀ u ∈ Icc s (s + L), ‖(c.curve u).2‖ ≤ ρ := by
        intro u hu
        exact hrρ u (c.inDomain_mono hend (hs.1.trans hu.1) hu.2)
      simpa [ForwardCurve.map] using hb c hc s hs hsa' L hL hend hnorm) t ht
  have hz' : ‖(c.curve t).1‖ < ε / 2 := by simpa [ForwardCurve.map] using hz
  have hr' : ‖(c.curve t).2‖ < ε / 2 :=
    (hnormal c hc t ht).trans_lt ((norm_snd_le _).trans_lt
      (hi.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
  have hnorm : ‖c.curve t‖ < ε := by
    rw [Prod.norm_def]
    exact (max_lt hz' hr').trans (half_lt_self hε)
  simpa using hnorm

/-- Normal decay, finite-time return estimates and compact continuation imply
local asymptotic stability for the entire family of trajectories. -/
theorem strongLAS_of_finite_blocks
    {S : Set (ForwardCurve (E × ℝ))} {R : ℝ} (hR : 0 < R)
    (hnormal : NormalBound S) (hblocks : TangentBlockProperty S)
    (hcontinue : BoundedContinuation S R)
    (hconverge : NormalConvergence S)
    (hendpoint : TangentEndpointProperty S R)
    (hshift : GlobalShiftClosed S) : StrongLAS S 0 := by
  have hs := strongStable_of_finite_blocks hnormal hblocks
  refine ⟨hs, ?_⟩
  obtain ⟨δ₀, hδ₀, htrap⟩ := hs R hR
  refine ⟨δ₀, hδ₀, ?_⟩
  intro c hc hinit
  have hbound : ∀ t, c.InDomain t → ‖c.curve t‖ ≤ R := by
    intro t ht
    exact le_of_lt (by simpa using htrap c hc hinit t ht)
  have hg : c.IsGlobal := hcontinue c hc hbound
  refine ⟨hg, tendsto_of_futureStable_of_enters (hs.futureStable hshift hc hg) ?_⟩
  intro δ hδ
  obtain ⟨ρ, hρ, T, hT, he⟩ := hendpoint (δ / 2) (half_pos hδ)
  obtain ⟨s₀, hs₀⟩ := Metric.tendsto_atTop.mp (hconverge c hc hg)
    (min ρ (δ / 2)) (lt_min hρ (half_pos hδ))
  let s := max s₀ 0
  have hs0 : 0 ≤ s := le_max_right _ _
  have hlate : ∀ t, s ≤ t → ‖(c.curve t).2‖ < min ρ (δ / 2) := by
    intro t ht
    simpa using hs₀ t ((le_max_left _ _).trans ht)
  have hz : ‖(c.curve (s + T)).1‖ < δ / 2 :=
    he c hc hg s hs0
      (fun t ht => hbound t (c.inDomain_of_global hg (hs0.trans ht)))
      (fun t ht => (hlate t ht).le.trans (min_le_left _ _))
  have hr : ‖(c.curve (s + T)).2‖ < δ / 2 :=
    (hlate (s + T) (by linarith)).trans_le (min_le_right _ _)
  refine ⟨s + T, by linarith, ?_⟩
  have hsmall : ‖c.curve (s + T)‖ < δ := by
    rw [Prod.norm_def]
    exact (max_lt hz hr).trans (half_lt_self hδ)
  simpa using hsmall

end CascadeAssembly

section ObservationGraph

variable {E : Type*} [PseudoMetricSpace E]

def graphLift (h : E → ℝ) (c : ForwardCurve E) : ForwardCurve (E × ℝ) :=
  c.map (fun x => (x, h x))

def GraphLiftFamily (h : E → ℝ) (S : Set (ForwardCurve E)) : Set (ForwardCurve (E × ℝ)) :=
  graphLift h '' S

omit [PseudoMetricSpace E] in
theorem graphLiftFamily_globalShiftClosed {h : E → ℝ} {S : Set (ForwardCurve E)}
    (hs : GlobalShiftClosed S) : GlobalShiftClosed (GraphLiftFamily h S) := by
  rintro _ ⟨c, hc, rfl⟩ hg s hs0
  exact ⟨globalShift c s, hs c hc hg s hs0, rfl⟩

/-- Adding a continuous observation to the state preserves all-solution LAS,
including lifetimes. In particular the scalar CBF value can be appended
without constructing a coordinate diffeomorphism. -/
theorem strongLAS_graphLift_iff {h : E → ℝ} {p : E} (hh : ContinuousAt h p)
    {S : Set (ForwardCurve E)} :
    StrongLAS (GraphLiftFamily h S) (p, h p) ↔ StrongLAS S p := by
  constructor
  · intro hf
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hb⟩ := hf.1 ε hε
      obtain ⟨η, hη, hhη⟩ := Metric.continuousAt_iff.mp hh δ hδ
      refine ⟨min δ η, lt_min hδ hη, ?_⟩
      intro c hc hi t ht
      have hinit : dist ((graphLift h c).curve 0) (p, h p) < δ := by
        change max (dist (c.curve 0) p) (dist (h (c.curve 0)) (h p)) < δ
        exact max_lt (hi.trans_le (min_le_left _ _)) (hhη (hi.trans_le (min_le_right _ _)))
      have hv := hb (graphLift h c) ⟨c, hc, rfl⟩ hinit t ht
      exact (le_max_left _ _).trans_lt hv
    · obtain ⟨δ, hδ, hb⟩ := hf.2
      obtain ⟨η, hη, hhη⟩ := Metric.continuousAt_iff.mp hh δ hδ
      refine ⟨min δ η, lt_min hδ hη, ?_⟩
      intro c hc hi
      have hinit : dist ((graphLift h c).curve 0) (p, h p) < δ := by
        change max (dist (c.curve 0) p) (dist (h (c.curve 0)) (h p)) < δ
        exact max_lt (hi.trans_le (min_le_left _ _)) (hhη (hi.trans_le (min_le_right _ _)))
      obtain ⟨hg, hl⟩ := hb (graphLift h c) ⟨c, hc, rfl⟩ hinit
      refine ⟨hg, ?_⟩
      simpa [graphLift, ForwardCurve.map, Function.comp_def] using
        (continuous_fst.tendsto (p, h p)).comp hl
  · intro hs
    constructor
    · intro ε hε
      obtain ⟨η, hη, hhη⟩ := Metric.continuousAt_iff.mp hh ε hε
      obtain ⟨δ, hδ, hb⟩ := hs.1 (min ε η) (lt_min hε hη)
      refine ⟨δ, hδ, ?_⟩
      rintro _ ⟨c, hc, rfl⟩ hi t ht
      have hi' : dist (c.curve 0) p < δ := (le_max_left _ _).trans_lt hi
      have hv := hb c hc hi' t ht
      change max (dist (c.curve t) p) (dist (h (c.curve t)) (h p)) < ε
      exact max_lt (hv.trans_le (min_le_left _ _)) (hhη (hv.trans_le (min_le_right _ _)))
    · obtain ⟨δ, hδ, hb⟩ := hs.2
      refine ⟨δ, hδ, ?_⟩
      rintro _ ⟨c, hc, rfl⟩ hi
      have hi' : dist (c.curve 0) p < δ := (le_max_left _ _).trans_lt hi
      obtain ⟨hg, hl⟩ := hb c hc hi'
      refine ⟨hg, ?_⟩
      exact hl.prodMk_nhds (hh.tendsto.comp hl)

end ObservationGraph

section RobustBlockBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Dynamics of the first coordinate of an observed trajectory. The second
coordinate may be an observation such as h(x), rather than an independent
state coordinate. -/
def ObservationDynamics (S : Set (ForwardCurve (E × ℝ))) (B : E × ℝ → E) : Prop :=
  ∀ c ∈ S, ∀ t, c.InDomain t →
    HasDerivWithinAt (fun u => (c.curve u).1) (B (c.curve t)) (Ici 0) t

def ObservationRelation (S : Set (ForwardCurve (E × ℝ))) (C : Set (E × ℝ)) : Prop :=
  ∀ c ∈ S, ∀ t, c.InDomain t → c.curve t ∈ C

/-- The exact unforced reference-segment statement consumed by the proved
robustness theorem in TimeBlocks. -/
def ReferenceEstimate (B : E × ℝ → E) (C : Set (E × ℝ))
    (A : Set E) (T e d : ℝ) : Prop :=
  ∀ L ∈ Icc 0 T, ∀ g : ℝ → E, ContinuousOn g (Icc 0 1) →
    (∀ t ∈ Icc (0 : ℝ) 1, g t ∈ closedBall 0 e ∧ (g t, (0 : ℝ)) ∈ C) →
    (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (L • B (g t, 0)) t) →
    g 0 ∈ A → ‖g 1‖ < e ∧ (L = T → ‖g 1‖ < d)

theorem observed_return_block
    {S : Set (ForwardCurve (E × ℝ))} {B : E × ℝ → E} {C : Set (E × ℝ)}
    (hdyn : ObservationDynamics S B) (hrel : ObservationRelation S C)
    {A : Set E} (hA : IsClosed A) {T R e d : ℝ} (hR : 0 < R)
    (hstart : ∀ z ∈ A, ‖z‖ < e)
    (hB : ContinuousOn B (closedBall 0 e ×ˢ Icc (-R) R)) (hC : IsClosed C)
    (href : ReferenceEstimate B C A T e d) :
    ∃ ρ > 0, ∀ c ∈ S, ∀ s, c.InDomain s →
      ∀ L ∈ Icc 0 T, c.InDomain (s + L) →
        (∀ t ∈ Icc s (s + L), ‖(c.curve t).2‖ ≤ ρ) → (c.curve s).1 ∈ A →
        (∀ t ∈ Icc s (s + L), ‖(c.curve t).1‖ < e) ∧
        (L = T → ‖(c.curve (s + L)).1‖ < d) := by
  obtain ⟨ρ, hρ, hb⟩ := robust_return_block hA hR hstart hB hC href
  refine ⟨ρ, hρ, ?_⟩
  intro c hc s hs L hL hend hr hz
  have hdom (t : ℝ) (ht : t ∈ Icc 0 L) : c.InDomain (t + s) :=
    c.inDomain_mono hend (add_nonneg ht.1 hs.1) (by linarith [ht.2])
  have htime (t : ℝ) (ht : t ∈ Icc 0 L) : t + s ∈ Icc s (s + L) := by
    constructor <;> linarith [ht.1, ht.2]
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 L) :
      HasDerivWithinAt (fun u => (c.curve (u + s)).1)
        (B ((c.curve (t + s)).1, (c.curve (t + s)).2)) (Icc 0 L) t := by
    have ha : HasDerivWithinAt (fun u : ℝ => u + s) 1 (Icc 0 L) t :=
      ((hasDerivAt_id t).add_const s).hasDerivWithinAt
    have hm : MapsTo (fun u : ℝ => u + s) (Icc 0 L) (Ici 0) :=
      fun u hu => add_nonneg hu.1 hs.1
    simpa [Function.comp_def] using (hdyn c hc (t + s) (hdom t ht)).scomp t ha hm
  have h := hb L hL (fun t => (c.curve (t + s)).1) (fun t => (c.curve (t + s)).2)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hr (t + s) (htime t ht))
    (fun t ht _ => hrel c hc (t + s) (hdom t ht)) hderiv (by simpa using hz)
  constructor
  · intro t ht
    have hu : t - s ∈ Icc 0 L := by constructor <;> linarith [ht.1, ht.2]
    simpa using h.1 (t - s) hu
  · intro he
    simpa [add_comm] using h.2 he

/-- Reference estimates at arbitrarily small radii imply the exact finite
blocks required for strong stability. Only local continuity in one cylinder
is assumed. -/
theorem tangentBlockProperty_of_referenceEstimates
    {S : Set (ForwardCurve (E × ℝ))} {B : E × ℝ → E} {C : Set (E × ℝ)}
    (hdyn : ObservationDynamics S B) (hrel : ObservationRelation S C)
    {Rbar Rn : ℝ} (hRbar : 0 < Rbar) (hRn : 0 < Rn)
    (hB : ContinuousOn B (closedBall 0 Rbar ×ˢ Icc (-Rn) Rn)) (hC : IsClosed C)
    (href : ∀ e, 0 < e → e ≤ Rbar →
      ∃ a > 0, a < e ∧ ∃ T > 0,
        ReferenceEstimate B C (closedBall 0 a) T e a) :
    TangentBlockProperty S := by
  intro ε hε
  let e := min (ε / 2) (Rbar / 2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hRbar)
  have heR : e ≤ Rbar := (min_le_right _ _).trans (half_le_self hRbar.le)
  obtain ⟨a, ha, hae, T, hT, hreference⟩ := href e he heR
  have hcont : ContinuousOn B (closedBall 0 e ×ˢ Icc (-Rn) Rn) :=
    hB.mono (Set.prod_mono (closedBall_subset_closedBall heR) Subset.rfl)
  obtain ⟨ρ, hρ, hb⟩ := observed_return_block hdyn hrel isClosed_closedBall hRn
    (fun z hz => (show ‖z‖ ≤ a by simpa using hz).trans_lt hae) hcont hC hreference
  refine ⟨a, ha, ρ, hρ, T, hT, ?_⟩
  intro c hc s hs hz L hL hend hr
  have h := hb c hc s hs L hL hend hr (by simpa using hz)
  refine ⟨(h.1 (s + L) ⟨by linarith [hL.1], le_rfl⟩).trans_le
      ((min_le_left _ _).trans (half_le_self hε.le)), ?_⟩
  intro heq
  exact (h.2 heq).le

theorem tangentEndpointProperty_of_referenceEstimates
    {S : Set (ForwardCurve (E × ℝ))} {B : E × ℝ → E} {C : Set (E × ℝ)}
    (hdyn : ObservationDynamics S B) (hrel : ObservationRelation S C)
    {Rbar Rn R : ℝ} (hRn : 0 < Rn) (hRR : R < Rbar)
    (hB : ContinuousOn B (closedBall 0 Rbar ×ˢ Icc (-Rn) Rn)) (hC : IsClosed C)
    (href : ∀ d > 0, ∃ T > 0,
      ReferenceEstimate B C (closedBall 0 R) T Rbar d) :
    TangentEndpointProperty S R := by
  intro d hd
  obtain ⟨T, hT, hreference⟩ := href d hd
  obtain ⟨ρ, hρ, hb⟩ := observed_return_block hdyn hrel isClosed_closedBall hRn
    (fun z hz => (show ‖z‖ ≤ R by simpa using hz).trans_lt hRR) hB hC hreference
  refine ⟨ρ, hρ, T, hT, ?_⟩
  intro c hc hg s hs hbound hsmall
  have hsdom := c.inDomain_of_global hg hs
  have hend := c.inDomain_of_global hg (show 0 ≤ s + T by linarith)
  have hz : (c.curve s).1 ∈ closedBall 0 R := by
    simpa using (norm_fst_le (c.curve s)).trans (hbound s le_rfl)
  exact (hb c hc s hsdom T ⟨hT.le, le_rfl⟩ hend
    (fun t ht => hsmall t ht.1) hz).2 rfl

end RobustBlockBridge

section NormalEquationBridge

variable {E : Type*}

def NormalEquation (S : Set (ForwardCurve (E × ℝ))) (α : ℝ → ℝ) : Prop :=
  ∀ c ∈ S, ∀ t, c.InDomain t →
    HasDerivWithinAt (fun u => (c.curve u).2) (-α ((c.curve t).2)) (Ici 0) t

theorem normalBound_of_equation_of_traceSign
    {S : Set (ForwardCurve (E × ℝ))} {α : ℝ → ℝ}
    (heq : NormalEquation S α)
    (hsign : ∀ c ∈ S, ∀ t, c.InDomain t →
      0 ≤ (c.curve t).2 * α ((c.curve t).2)) : NormalBound S := by
  intro c hc t ht
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivWithinAt (fun u => (c.curve u).2)
        (-α ((c.curve s).2)) (Icc 0 t) s :=
    (heq c hc s (c.inDomain_mono ht hs.1 hs.2)).mono Icc_subset_Ici_self
  have ha := normal_sq_antitone (convex_Icc (0 : ℝ) t) hd
    (fun s hs => hsign c hc s (c.inDomain_mono ht hs.1 hs.2))
  have h := ha (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1) ht.1
  have hsq : ((c.curve t).2)^2 ≤ ((c.curve 0).2)^2 := by simpa [pow_two] using h
  simpa only [Real.norm_eq_abs] using (sq_le_sq.mp hsq)

theorem normalBound_of_equation
    {S : Set (ForwardCurve (E × ℝ))} {α : ℝ → ℝ}
    (heq : NormalEquation S α) (hsign : ∀ x : ℝ, 0 ≤ x * α x) :
    NormalBound S := by
  intro c hc t ht
  have hd (s : ℝ) (hs : s ∈ Icc 0 t) :
      HasDerivWithinAt (fun u => (c.curve u).2)
        (-α ((c.curve s).2)) (Icc 0 t) s :=
    (heq c hc s (c.inDomain_mono ht hs.1 hs.2)).mono Icc_subset_Ici_self
  have ha := normal_sq_antitone (convex_Icc (0 : ℝ) t) hd (fun s _ => hsign ((c.curve s).2))
  have h := ha (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1) ht.1
  have hsq : ((c.curve t).2)^2 ≤ ((c.curve 0).2)^2 := by simpa [pow_two] using h
  simpa only [Real.norm_eq_abs] using (sq_le_sq.mp hsq)

theorem normalConvergence_of_equation
    {S : Set (ForwardCurve (E × ℝ))} {α : ℝ → ℝ}
    (heq : NormalEquation S α) (hα : Continuous α)
    (hsign : ∀ x : ℝ, x ≠ 0 → 0 < x * α x) :
    NormalConvergence S := by
  have hnonneg : ∀ x : ℝ, 0 ≤ x * α x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hsign x hx).le
  have hb := normalBound_of_equation heq hnonneg
  intro c hc hg
  apply normal_tendsto_zero (R := ‖(c.curve 0).2‖) hα.continuousOn
  · intro t ht
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using (hb c hc t (c.inDomain_of_global hg ht)))
  · intro t ht
    exact heq c hc t (c.inDomain_of_global hg ht)
  · intro x _ hx
    exact hsign x hx

/-- Only the values of alpha in an open normal neighborhood are used. Each
trajectory has its own compact invariant normal interval, whose radius is
the magnitude of its initial normal value. -/
theorem normalConvergence_of_equation_on
    {S : Set (ForwardCurve (E × ℝ))} {α : ℝ → ℝ} {ρ : ℝ}
    (heq : NormalEquation S α) (hα : ContinuousOn α (Ioo (-ρ) ρ))
    (hrange : ∀ c ∈ S, ∀ t, c.InDomain t → |(c.curve t).2| < ρ)
    (hsign : ∀ x ∈ Ioo (-ρ) ρ, x ≠ 0 → 0 < x * α x) :
    NormalConvergence S := by
  have htrace : ∀ c ∈ S, ∀ t, c.InDomain t →
      0 ≤ (c.curve t).2 * α ((c.curve t).2) := by
    intro c hc t ht
    by_cases hz : (c.curve t).2 = 0
    · simp [hz]
    · exact (hsign _ (abs_lt.mp (hrange c hc t ht)) hz).le
  have hb := normalBound_of_equation_of_traceSign heq htrace
  intro c hc hg
  let R := ‖(c.curve 0).2‖
  have hRρ : R < ρ := by
    simpa only [R, Real.norm_eq_abs] using hrange c hc 0 c.zero_inDomain
  have hsub : Icc (-R) R ⊆ Ioo (-ρ) ρ := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  apply normal_tendsto_zero (R := R) (hα.mono hsub)
  · intro t ht
    exact abs_le.mp (by simpa only [R, Real.norm_eq_abs] using
      (hb c hc t (c.inDomain_of_global hg ht)))
  · intro t ht
    exact heq c hc t (c.inDomain_of_global hg ht)
  · intro x hx hx0
    exact hsign x (hsub hx) hx0

theorem normalBounds_of_local_equation
    {S : Set (ForwardCurve (E × ℝ))} {α : ℝ → ℝ} {ρ : WithTop ℝ}
    (heq : NormalEquation S α)
    (hrange : ∀ c ∈ S, ∀ t, c.InDomain t → (c.curve t).2 ∈ barrierInterval ρ)
    (cα : ContinuousOn α (barrierInterval ρ))
    (restore : ∀ r ∈ barrierInterval ρ, r ≠ 0 → 0 < r * α r) :
    NormalBound S ∧ NormalConvergence S := by
  have htrace : ∀ c ∈ S, ∀ t, c.InDomain t →
      0 ≤ (c.curve t).2 * α ((c.curve t).2) := by
    intro c hc t ht
    by_cases hz : (c.curve t).2 = 0
    · simp [hz]
    · exact (restore _ (hrange c hc t ht) hz).le
  refine ⟨normalBound_of_equation_of_traceSign heq htrace, ?_⟩
  cases ρ using WithTop.recTopCoe with
  | top =>
    exact normalConvergence_of_equation heq (continuousOn_univ.mp cα)
      (fun r => restore r (mem_univ r))
  | coe r =>
    exact normalConvergence_of_equation_on (ρ := r) heq cα
      (fun c hc t ht => abs_lt.mpr (hrange c hc t ht)) restore

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem observationDynamics_graphLift_on
    {F : E → E} {U : Set E} {h : E → ℝ} {B : E × ℝ → E}
    (hB : ∀ x ∈ U, B (x, h x) = F x) :
    ObservationDynamics (GraphLiftFamily h (MaximalSolutionsOn F U)) B := by
  rintro _ ⟨c, hc, rfl⟩ t ht
  have hd := hc.1.1 t ht
  have he := hB (c.curve t) (hc.1.2 t ht)
  simpa [graphLift, ForwardCurve.map, he] using hd

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem observationRelation_graphLift
    {S : Set (ForwardCurve E)} {h : E → ℝ} :
    ObservationRelation (GraphLiftFamily h S) {q : E × ℝ | q.2 = h q.1} := by
  rintro _ ⟨c, hc, rfl⟩ t ht
  rfl

theorem normalEquation_graphLift_on
    {F : E → E} {U : Set E} {α : ℝ → ℝ}
    {H : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hd : ∀ x ∈ U, HasFDerivAt H (D x) x)
    (heq : ∀ x ∈ U, D x (F x) = -α (H x)) :
    NormalEquation (GraphLiftFamily H (MaximalSolutionsOn F U)) α := by
  rintro _ ⟨c, hc, rfl⟩ t ht
  have hx := hc.1.2 t ht
  have hderiv := (hd (c.curve t) hx).comp_hasDerivWithinAt t (hc.1.1 t ht)
  simpa [graphLift, ForwardCurve.map, Function.comp_def, heq (c.curve t) hx] using hderiv

end NormalEquationBridge

section ReferenceAssembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Local continuous reduction engine. All dynamical estimates in this theorem
are obtained from the exact normal equation and unforced reference segments.
No Lipschitz continuity, unique solutions, Jacobians, or strict normal decay
rate is assumed. The reference-segment estimates are the explicit interface
to the LAS assumption on the reference/boundary system. -/
theorem strongLAS_of_referenceEstimates
    {S : Set (ForwardCurve (E × ℝ))} {B : E × ℝ → E} {C : Set (E × ℝ)}
    {α : ℝ → ℝ} {Rbar Rn R : ℝ}
    (hRbar : 0 < Rbar) (hRn : 0 < Rn) (hR : 0 < R) (hRR : R < Rbar)
    (hdyn : ObservationDynamics S B) (hrel : ObservationRelation S C)
    (hB : ContinuousOn B (closedBall 0 Rbar ×ˢ Icc (-Rn) Rn)) (hC : IsClosed C)
    (heq : NormalEquation S α) (hα : ContinuousOn α (Ioo (-Rn) Rn))
    (hrange : ∀ c ∈ S, ∀ t, c.InDomain t → |(c.curve t).2| < Rn)
    (hsign : ∀ x ∈ Ioo (-Rn) Rn, x ≠ 0 → 0 < x * α x)
    (hcontinue : BoundedContinuation S R) (hshift : GlobalShiftClosed S)
    (hrefBlocks : ∀ e, 0 < e → e ≤ Rbar →
      ∃ a > 0, a < e ∧ ∃ T > 0,
        ReferenceEstimate B C (closedBall 0 a) T e a)
    (hrefEndpoints : ∀ d > 0, ∃ T > 0,
      ReferenceEstimate B C (closedBall 0 R) T Rbar d) :
    StrongLAS S 0 := by
  have htrace : ∀ c ∈ S, ∀ t, c.InDomain t →
      0 ≤ (c.curve t).2 * α ((c.curve t).2) := by
    intro c hc t ht
    by_cases hz : (c.curve t).2 = 0
    · simp [hz]
    · exact (hsign _ (abs_lt.mp (hrange c hc t ht)) hz).le
  exact strongLAS_of_finite_blocks hR
    (normalBound_of_equation_of_traceSign heq htrace)
    (tangentBlockProperty_of_referenceEstimates hdyn hrel hRbar hRn hB hC hrefBlocks)
    hcontinue (normalConvergence_of_equation_on heq hα hrange hsign)
    (tangentEndpointProperty_of_referenceEstimates hdyn hrel hRn hRR hB hC hrefEndpoints)
    hshift

end ReferenceAssembly

end CBFIndependence
