import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Tactic.Ring

namespace CBFIndependence
open Set
variable {X W E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- State-dependent affine plant and barrier data on a parameter domain.
For an actual CBF take n(x) = Dh(x) and b(x) = α(h(x)). -/
def residual (f : X → E) (g : X → W →L[ℝ] E) (n : X → E →L[ℝ] ℝ)
    (b : X → ℝ) (x : X) (w : W) := n x (f x + g x w) + b x

theorem continuous_residual {f : X → E} {g : X → W →L[ℝ] E}
    {n : X → E →L[ℝ] ℝ} {b : X → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hn : Continuous n) (hb : Continuous b) :
    Continuous (fun p : X × W => residual f g n b p.1 p.2) :=
  ((hn.comp continuous_fst).clm_apply ((hf.comp continuous_fst).add
    ((hg.comp continuous_fst).clm_apply continuous_snd))).add (hb.comp continuous_fst)

omit [TopologicalSpace X] in
theorem neg_residual_convex (f : X → E) (g : X → W →L[ℝ] E)
    (n : X → E →L[ℝ] ℝ) (b : X → ℝ) (x : X) :
    ConvexOn ℝ univ (fun w => -residual f g n b x w) := by
  let A : W →ₗ[ℝ] ℝ := -((n x).comp (g x)).toLinearMap
  convert (A.convexOn (convex_univ : Convex ℝ (univ : Set W))).add_const
    (-(n x (f x) + b x)) using 1
  ext w
  simp [A, residual]
  ring

end CBFIndependence
