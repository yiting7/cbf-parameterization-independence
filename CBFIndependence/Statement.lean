import CBFIndependence.AffineResidual
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Basic

/-!
# CBF-pair independence of local asymptotic stability

This file contains the definitions, hypotheses and conclusions of the theorem.
The final declaration is `CBFIndependenceStatement`. Its proof is
`CBFIndependence.undesirable_equilibrium_las_pair_independent`. The project root
checks that proof against this statement when you run `lake build`.

Let `p` be an equilibrium of the first filtered system with nonzero nominal
velocity. The theorem locates `p` on the common boundary and identifies a
neighborhood on which local asymptotic stability for either filter is
equivalent to stability of the same boundary dynamics. Initial states for the
ambient result may lie on either side of the boundary.
-/

namespace CBFIndependence
open Set Filter Topology
open scoped ENNReal
noncomputable section

/-! ## The nominal and filtered optimization problems -/

namespace Optimization
variable {X E : Type*}

/-- Feasibility for finitely many scalar inequalities. -/
def Feasible {q : ℕ} (c : Fin q → X → E → ℝ) (x : X) : Set E :=
  {z | ∀ j, c j x z ≤ 0}

/-- Strict feasibility (Slater's condition at the displayed decision vector). -/
def StrictlyFeasible {q : ℕ} (c : Fin q → X → E → ℝ) (x : X) (z : E) : Prop :=
  ∀ j, c j x z < 0

/-- Global optimality includes membership in the feasible set. -/
def Minimizes (f : E → ℝ) (K : Set E) (z : E) : Prop :=
  z ∈ K ∧ ∀ y ∈ K, f z ≤ f y

/-- A total choice of optimizer.  The zero fallback is used only when the
optimization problem has no minimizer; all specification theorems below establish
existence before using this choice. -/
noncomputable def optimizer [Zero E] (f : E → ℝ) (K : Set E) : E := by
  classical
  exact if h : ∃ z, Minimizes f K z then Classical.choose h else 0

end Optimization
open Optimization

section Programs
variable {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The feasible set after adding one barrier with residual `c`. -/
def filtered (K : Set W) (c : W → ℝ) : Set W := {w | w ∈ K ∧ 0 ≤ c w}

/-- Feasibility together with global objective minimality. -/
def Solves (L : W → ℝ) (K : Set W) (w : W) : Prop := w ∈ K ∧ IsMinOn L K w

/-- At each state the cost is strongly convex in the decision and each original
constraint is convex. All are jointly continuous in the state and decision.
The modulus may depend on the state; `Fin 0` permits no original constraints. -/
structure Program (X W : Type*) [TopologicalSpace X]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (q : ℕ) where
  cost : X → W → ℝ
  cost_cont : Continuous (fun p : X × W => cost p.1 p.2)
  strong : ∀ x, ∃ m : ℝ, 0 < m ∧ StrongConvexOn univ m (cost x)
  constraints : Fin q → X → W → ℝ
  joint_cont : ∀ j, Continuous (fun p : X × W => constraints j p.1 p.2)
  convex : ∀ x j, ConvexOn ℝ univ (constraints j x)

namespace Program
variable {q : ℕ} (P : Program X W q)

def domain (x : X) := Feasible P.constraints x
def decision (x : X) := optimizer (P.cost x) (P.domain x)
def slater (x : X) := ∃ w, StrictlyFeasible P.constraints x w

/-- Add a barrier with continuous residual and affine dependence on the
decision. The sign convention for the original constraints is ≤ 0. -/
def addBarrier (c : X → W → ℝ) (cc : Continuous (fun p : X × W => c p.1 p.2))
    (cv : ∀ x, ConvexOn ℝ univ (fun w => -c x w)) : Program X W (q+1) where
  cost := P.cost
  cost_cont := P.cost_cont
  strong := P.strong
  constraints := Fin.cons (fun x w => -c x w) P.constraints
  joint_cont j := Fin.cases cc.neg P.joint_cont j
  convex x j := Fin.cases (cv x) (P.convex x) j

end Program
end Programs

section Controllers
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {U : Set E} {q : ℕ}

/-- The scalar domain of a CBF pair. A finite radius gives the open interval
(-r,r), and an infinite radius gives the entire real line. -/
def barrierInterval : WithTop ℝ → Set ℝ :=
  WithTop.recTopCoe univ (fun r => Ioo (-r) r)

@[simp] theorem barrierInterval_coe (r : ℝ) :
    barrierInterval (r : WithTop ℝ) = Ioo (-r) r := rfl

@[simp] theorem barrierInterval_top : barrierInterval ⊤ = (univ : Set ℝ) := rfl

/-- Each barrier has its own radius in (0,+∞]. The range of h on U lies in
its scalar domain, where α is continuous and strictly restoring away from zero. -/
structure Barrier (U : Set E) where
  h : E → ℝ
  smooth : ContDiffOn ℝ 1 h U
  α : ℝ → ℝ
  ρ : WithTop ℝ
  radius_pos : 0 < ρ
  range_ok : MapsTo h U (barrierInterval ρ)
  cont : ContinuousOn α (barrierInterval ρ)
  zero : α 0 = 0
  restoring : ∀ r ∈ barrierInterval ρ, r ≠ 0 → 0 < r * α r

/-- For the usual auxiliary decision `w = (u, δ)`, take
`input x w = g(x)u`. Both filters use this same affine plant. -/
structure Plant (U : Set E) (W : Type*) [NormedAddCommGroup W] [NormedSpace ℝ W] where
  drift : U → E
  input : U → W →L[ℝ] E
  drift_cont : Continuous drift
  input_cont : Continuous input

def Plant.velocity (A : Plant U W) (x : U) (w : W) := A.drift x + A.input x w

namespace Barrier
variable (H : Barrier U) (oU : IsOpen U) (A : Plant U W) (P : Program U W q)

def normal (x : U) := fderiv ℝ H.h (x:E)
def offset (x : U) := H.α (H.h x)
def cbf := residual A.drift A.input H.normal H.offset

/-- The filtered feasible set adds the half-space where this residual is nonnegative. -/
theorem cbf_value (x : U) (w : W) :
    H.cbf A x w = fderiv ℝ H.h (x : E) (A.drift x + A.input x w) + H.α (H.h x) := rfl

include oU in
theorem normal_cont : Continuous H.normal :=
  continuousOn_iff_continuous_restrict.mp (H.smooth.continuousOn_fderiv_of_isOpen oU le_rfl)
theorem offset_cont : Continuous H.offset :=
  continuousOn_iff_continuous_restrict.mp (H.cont.comp H.smooth.continuousOn H.range_ok)

def program : Program U W (q+1) :=
  P.addBarrier (H.cbf A)
    (continuous_residual A.drift_cont A.input_cont (H.normal_cont oU) H.offset_cont)
    (neg_residual_convex _ _ _ _)

/-- Apply the plant to the optimizer of the filtered problem. -/
def field (x : U) := A.velocity x ((H.program oU A P).decision x)

/-- Strict feasibility is a pointwise assumption. A single test decision must
make every original constraint and the added CBF inequality strict. -/
theorem slater_iff {x : U} :
    (H.program oU A P).slater x ↔
      ∃ w, (∀ j, P.constraints j x w < 0) ∧ 0 < H.cbf A x w := by
  simp [Program.slater, StrictlyFeasible, program, Program.addBarrier,
    Fin.forall_fin_succ, and_comm]

end Barrier

/-- The field on the open set is extended by zero solely to give it ambient
type. Every solution in the theorem takes values in a subset of `U`. -/
def ambientField (F : U → E) (x : E) : E := by
  classical
  exact if hx : x ∈ U then F ⟨x,hx⟩ else 0

end Controllers

/-! ## Forward solutions and local asymptotic stability

The lifetime is positive and may be infinite. Only the half-open time interval
from zero to that lifetime enters the ODE or its extension relation. A solution
on a set `V` is maximal among extensions whose states stay in `V`. -/

/-- A forward curve with an explicit positive, possibly infinite lifetime. -/
structure ForwardCurve (E : Type*) where
  curve : ℝ → E
  lifetime : ℝ≥0∞
  positive_lifetime : 0 < lifetime

namespace ForwardCurve

variable {E : Type*}

def InDomain (c : ForwardCurve E) (t : ℝ) : Prop :=
  0 ≤ t ∧ ENNReal.ofReal t < c.lifetime

def IsGlobal (c : ForwardCurve E) : Prop := c.lifetime = ⊤

/-- `d` extends `c` without changing any state in `c`'s domain. -/
def Extends (d c : ForwardCurve E) : Prop :=
  c.lifetime ≤ d.lifetime ∧ ∀ t, c.InDomain t → d.curve t = c.curve t

end ForwardCurve

section Solutions
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A classical forward solution on its lifetime; no uniqueness is required. -/
def SolvesODE (F : E → E) (c : ForwardCurve E) : Prop :=
  ∀ t, c.InDomain t →
    HasDerivWithinAt c.curve (F (c.curve t)) (Ici 0) t

/-- Solutions of the vector field with a specified state-space domain. -/
def SolvesODEOn (F : E → E) (U : Set E) (c : ForwardCurve E) : Prop :=
  SolvesODE F c ∧ ∀ t, c.InDomain t → c.curve t ∈ U

def MaximalSolutionOn (F : E → E) (U : Set E) (c : ForwardCurve E) : Prop :=
  SolvesODEOn F U c ∧ ∀ d, SolvesODEOn F U d → d.Extends c → d.lifetime = c.lifetime

def MaximalSolutionsOn (F : E → E) (U : Set E) : Set (ForwardCurve E) :=
  {c | MaximalSolutionOn F U c}

/-- Maximal solutions in the state domain whose initial point belongs to Bdy. -/
def MaximalSolutionsFromOn (F : E → E) (U Bdy : Set E) : Set (ForwardCurve E) :=
  {c | MaximalSolutionOn F U c ∧ c.curve 0 ∈ Bdy}

end Solutions

section Stability
variable {E : Type*} [PseudoMetricSpace E]

/-- Stability is quantified over every curve in the specified solution family. -/
def StrongStable (S : Set (ForwardCurve E)) (p : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ c ∈ S,
    dist (c.curve 0) p < δ →
    ∀ t, c.InDomain t → dist (c.curve t) p < ε

/-- Strong attractivity includes forward completeness of every nearby solution. -/
def StrongAttractive (S : Set (ForwardCurve E)) (p : E) : Prop :=
  ∃ δ > 0, ∀ c ∈ S,
    dist (c.curve 0) p < δ →
    c.IsGlobal ∧ Tendsto c.curve atTop (𝓝 p)

def StrongLAS (S : Set (ForwardCurve E)) (p : E) : Prop :=
  StrongStable S p ∧ StrongAttractive S p

end Stability

/-! ## Conclusions on the common neighborhood

The optimizer, activity and boundary statements below are conclusions. All three
controllers are well posed at every point of a single open neighborhood.
The identity `Dh(x) F(x) = -α(h(x))` expresses local activity. At `h(x) = 0`
it gives tangency of the common boundary field. -/

namespace Program
variable {X W : Type*} [TopologicalSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W] {q : ℕ}

/-- Pointwise optimizer existence and uniqueness, the actual decision's
optimization specification, and continuity in the given parameter space. -/
structure WellposedAt (P : Program X W q) (x : X) : Prop where
  unique_solution : ∃! w, Solves (P.cost x) (P.domain x) w
  decision_solves : Solves (P.cost x) (P.domain x) (P.decision x)
  continuous : ContinuousAt P.decision x

end Program

section Conclusions
variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {U : Set E} {q : ℕ}

/-- All three actual optimization programs are well posed at every state in
`V`. Continuity is at the point in the original state subtype `U`, not merely
continuity along a chosen trajectory or a sequence. -/
structure ControllerProgramsWellposedOn (oU : IsOpen U) (H J : Barrier U)
    (A : Plant U W) (P : Program U W q) (V : Set E) : Prop where
  nominal : ∀ x : U, (x : E) ∈ V → P.WellposedAt x
  first : ∀ x : U, (x : E) ∈ V → (H.program oU A P).WellposedAt x
  second : ∀ x : U, (x : E) ∈ V → (J.program oU A P).WellposedAt x

/-- Here `offset x = α (h x)` for the barrier used by the field. -/
structure BarrierDynamics (F : E → E) (h offset : E → ℝ) (V : Set E) (S : Set E) : Prop where
  continuous : ContinuousOn F V
  zero_iff : ∀ x ∈ V, h x = 0 ↔ x ∈ frontier S
  active : ∀ x ∈ V, fderiv ℝ h x (F x) = -offset x

/-- Ambient, intrinsic boundary, and safe-initial-state stability all use
every maximal forward solution, with infinite lifetime required for attraction. -/
structure PairLAS (F G : E → E) (V S : Set E) (p : E) : Prop where
  common : EqOn F G (V ∩ frontier S)
  pair : StrongLAS (MaximalSolutionsOn F V) p ↔ StrongLAS (MaximalSolutionsOn G V) p
  first_boundary : StrongLAS (MaximalSolutionsOn F V) p ↔
    StrongLAS (MaximalSolutionsOn F (V ∩ frontier S)) p
  second_boundary : StrongLAS (MaximalSolutionsOn G V) p ↔
    StrongLAS (MaximalSolutionsOn F (V ∩ frontier S)) p
  first_safe : StrongLAS (MaximalSolutionsOn F V) p ↔ StrongLAS (MaximalSolutionsFromOn F V S) p
  second_safe : StrongLAS (MaximalSolutionsOn G V) p ↔ StrongLAS (MaximalSolutionsFromOn G V S) p
  first_exists : ∀ x ∈ V, ∃ c ∈ MaximalSolutionsOn F V, c.curve 0 = x
  second_exists : ∀ x ∈ V, ∃ c ∈ MaximalSolutionsOn G V, c.curve 0 = x

end Conclusions

/-! ## Intermediate results used in the proof

The first result uses only the optimization hypotheses and strict feasibility.
The second derives the active normal equation from a difference in plant
velocities. The third is a separate ODE result. Its active equation is proved
for each controller before that result is applied. -/

abbrev OptimizerWellposedStatement.{u,v} : Prop :=
  ∀ {E : Type u} {W : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ} (oU : IsOpen U) (H J : Barrier U)
    (A : Plant U W) (P : Program U W q) (p : U),
    (H.program oU A P).slater p → (J.program oU A P).slater p →
    ∃ V : Set E, IsOpen V ∧ (p : E) ∈ V ∧ V ⊆ U ∧ ControllerProgramsWellposedOn oU H J A P V

abbrev LocalActivityStatement.{u,v} : Prop :=
  ∀ {E : Type u} {W : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ} (H : Barrier U) (oU : IsOpen U)
    (A : Plant U W) (P : Program U W q) {p : U},
    (H.program oU A P).slater p → H.field oU A P p ≠ A.velocity p (P.decision p) →
    ∀ᶠ x in 𝓝 p, H.normal x (H.field oU A P x) = -H.α (H.h x)

abbrev BoundaryReductionStatement.{u} : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V Q Z : Set E} {F : E → E} {h : E → ℝ} {α : ℝ → ℝ} {p : E},
    IsOpen V → p ∈ V → IsCompact Q → V ⊆ Q → ContinuousOn h Q → h p = 0 → IsClosed Z →
    (∀ x ∈ V, h x = 0 ↔ x ∈ Z) → ContinuousOn F V →
    (∀ x ∈ V, DifferentiableAt ℝ h x) →
    (∀ x ∈ V, fderiv ℝ h x (F x) = -α (h x)) → ∀ {ρ : WithTop ℝ},
    MapsTo h V (barrierInterval ρ) → ContinuousOn α (barrierInterval ρ) →
    (∀ r ∈ barrierInterval ρ, r ≠ 0 → 0 < r * α r) →
    (StrongLAS (MaximalSolutionsOn F V) p ↔ StrongLAS (MaximalSolutionsOn F (V ∩ Z)) p)

/-! ## Main statement

The assumption `eqH` refers to the first filtered field and `nom` to the
unfiltered field. Boundary membership, both zero levels, both nonzero
derivatives, and equilibrium for the second field follow from these hypotheses.
In `PairLAS`, the boundary comparison uses the field of the first filter
restricted to `V ∩ frontier S`; `common` identifies it with the second.
The safe-initial-state comparisons still use maximal solutions in `V`.
-/

-- Hypothesis names are retained for named applications of the theorem.
set_option linter.unusedVariables false in
abbrev CBFIndependenceStatement.{u,v} : Prop :=
  ∀ {E : Type u} {W : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {U : Set E} {q : ℕ}
    (oU : IsOpen U) (S : Set E) (H J : Barrier U) (A : Plant U W) (P : Program U W q) (p : U)
    (sameH : ∀ x ∈ U, 0 ≤ H.h x ↔ x ∈ S) (sameJ : ∀ x ∈ U, 0 ≤ J.h x ↔ x ∈ S)
    (sH : (H.program oU A P).slater p) (sJ : (J.program oU A P).slater p)
    (eqH : H.field oU A P p = 0) (nom : A.velocity p (P.decision p) ≠ 0),
    (p:E) ∈ frontier S ∧ H.h p = 0 ∧ J.h p = 0 ∧ H.normal p ≠ 0 ∧ J.normal p ≠ 0 ∧
      J.field oU A P p = 0 ∧ ∃ V : Set E, IsOpen V ∧ (p:E) ∈ V ∧ V ⊆ U ∧
      ControllerProgramsWellposedOn oU H J A P V ∧
      BarrierDynamics (ambientField (H.field oU A P)) H.h (H.α ∘ H.h) V S ∧
      BarrierDynamics (ambientField (J.field oU A P)) J.h (J.α ∘ J.h) V S ∧
      PairLAS (ambientField (H.field oU A P)) (ambientField (J.field oU A P)) V S p

end
end CBFIndependence
