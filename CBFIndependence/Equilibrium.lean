import CBFIndependence.Controller
import CBFIndependence.Geometry

namespace CBFIndependence
open Filter Set Topology Geometry Optimization
noncomputable section

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Both the boundary location and regularity of both barriers are conclusions.
At the base state the vector field is written as a function of the decision.
Its affine form is used by the parametric controller to certify convexity. -/
theorem common_undesirable_equilibrium
    {K : Set W} {L : W → ℝ} (strict : StrictConvexOn ℝ K L)
    {p : E} {S : Set E} {h₁ h₂ : E → ℝ} {n₁ n₂ : E →L[ℝ] ℝ}
    (hd₁ : HasFDerivAt h₁ n₁ p) (hd₂ : HasFDerivAt h₂ n₂ p)
    (safe₁ : superlevel h₁ =ᶠ[𝓝 p] S) (safe₂ : superlevel h₂ =ᶠ[𝓝 p] S)
    {α₁ α₂ : ℝ → ℝ} (zero₁ : α₁ 0 = 0) (zero₂ : α₂ 0 = 0)
    (sign₁ : h₁ p ≠ 0 → 0 < h₁ p * α₁ (h₁ p))
    {A : W → E} (contA : Continuous A)
    (sl₁ : ∃ s ∈ K, 0 < n₁ (A s) + α₁ (h₁ p))
    (sl₂ : ∃ s ∈ K, 0 < n₂ (A s) + α₂ (h₂ p))
    (min₀ : Solves L K (optimizer L K))
    (min₁ : Solves L (filtered K (fun w => n₁ (A w) + α₁ (h₁ p)))
      (optimizer L (filtered K (fun w => n₁ (A w) + α₁ (h₁ p)))))
    (eqm : A (optimizer L (filtered K (fun w => n₁ (A w) + α₁ (h₁ p)))) = 0)
    (nom : A (optimizer L K) ≠ 0) :
    p ∈ frontier S ∧ h₁ p = 0 ∧ h₂ p = 0 ∧ n₁ ≠ 0 ∧ n₂ ≠ 0 ∧
      A (optimizer L (filtered K (fun w => n₂ (A w) + α₂ (h₂ p)))) = 0 := by
  obtain ⟨z₁, reg₁⟩ := zero_level_and_regular_of_undesirable sign₁ zero₁ strict
    contA min₁ min₀ eqm nom sl₁
  have bd₁ := mem_frontier_of_regular_zero hd₁ z₁ reg₁
  have bd := (mem_frontier_iff_of_eventuallyEq safe₁).mp bd₁
  have bd₂ := (mem_frontier_iff_of_eventuallyEq safe₂).mpr bd
  have z₂ := zero_of_mem_frontier_of_continuousAt hd₂.continuousAt bd₂
  have reg₂ : n₂ ≠ 0 := by
    rintro rfl
    obtain ⟨w, _, hw⟩ := sl₂
    simp [z₂, zero₂] at hw
  obtain ⟨c, hc, hn⟩ := normals_positive_multiple_of_eventuallyEq hd₁ hd₂ z₁ z₂
    (safe₁.trans safe₂.symm) reg₁ reg₂
  refine ⟨bd,z₁,z₂,reg₁,reg₂,?_⟩
  simpa only [z₁, z₂, zero₁, zero₂, add_zero, hn, ContinuousLinearMap.smul_apply,
    smul_eq_mul, filtered_scale hc] using eqm

end
end CBFIndependence
