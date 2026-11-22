import CBFIndependence.Cascade

namespace CBFIndependence
open Set Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def translateCurve (a : E) (c : ForwardCurve E) := c.map (fun x => x + a)

omit [NormedSpace ℝ E] in
@[simp] theorem translateCurve_val (a : E) (c : ForwardCurve E) (t : ℝ) :
    (translateCurve a c).curve t = c.curve t + a := rfl

omit [NormedSpace ℝ E] in
@[simp] theorem translateCurve_neg (a : E) (c : ForwardCurve E) :
    translateCurve (-a) (translateCurve a c) = c := by
  cases c
  simp [translateCurve, ForwardCurve.map, Function.comp_def]

omit [NormedSpace ℝ E] in
theorem translate_extends {c d : ForwardCurve E} (a : E) (he : d.Extends c) :
    (translateCurve a d).Extends (translateCurve a c) :=
  ⟨he.1, fun t ht => by simp only [translateCurve_val, he.2 t ht]⟩

theorem translate_solution {F : E → E} {D : Set E} (a : E) {c : ForwardCurve E}
    (hc : SolvesODEOn F D c) :
    SolvesODEOn (fun x => F (x-a)) {x | x-a ∈ D} (translateCurve a c) := by
  constructor
  · intro t ht
    simpa [translateCurve, ForwardCurve.map, Function.comp_def] using (hc.1 t ht).add_const a
  · intro t ht
    simpa using hc.2 t ht

theorem translate_maximal {F : E → E} {D : Set E} (a : E) {c : ForwardCurve E}
    (hc : MaximalSolutionOn F D c) :
    MaximalSolutionOn (fun x => F (x-a)) {x | x-a ∈ D} (translateCurve a c) := by
  refine ⟨translate_solution a hc.1, ?_⟩
  intro d hd he
  have hb := translate_solution (-a) hd
  have hback : SolvesODEOn F D (translateCurve (-a) d) := by simpa using hb
  exact hc.2 (translateCurve (-a) d) hback (by simpa using translate_extends (-a) he)

/-- Translation takes maximal trajectories to maximal trajectories and
preserves all distances from the equilibrium and every lifetime. -/
theorem translate_las {F : E → E} {D : Set E} {p : E} (a : E)
    (las : StrongLAS (MaximalSolutionsOn F D) p) :
    StrongLAS (MaximalSolutionsOn (fun x => F (x-a)) {x | x-a ∈ D}) (p+a) := by
  have back (c) (hc : c ∈ MaximalSolutionsOn (fun x => F (x-a)) {x | x-a ∈ D}) :
      translateCurve (-a) c ∈ MaximalSolutionsOn F D := by
    simpa [MaximalSolutionsOn] using translate_maximal (-a) hc
  have distance (x : E) : dist (x + -a) p = dist x (p+a) := by
    rw [← dist_add_right (x + -a) p a]; simp
  constructor
  · intro ε hε
    obtain ⟨δ,hδ,h⟩ := las.1 ε hε
    refine ⟨δ,hδ,?_⟩
    intro c hc hi t ht
    simpa only [translateCurve_val, distance] using h _ (back c hc)
      (by simpa only [translateCurve_val,distance] using hi) t ht
  · obtain ⟨δ,hδ,h⟩ := las.2
    refine ⟨δ,hδ,?_⟩
    intro c hc hi
    obtain ⟨full,lim⟩ := h _ (back c hc) (by simpa only [translateCurve_val,distance] using hi)
    exact ⟨full, by simpa [translateCurve, ForwardCurve.map, Function.comp_def] using lim.add_const a⟩

theorem recenter_las_iff {F : E → E} {D : Set E} (p : E) :
    StrongLAS (MaximalSolutionsOn (fun x => F (x+p)) {x | x+p ∈ D}) 0 ↔
      StrongLAS (MaximalSolutionsOn F D) p := by
  constructor
  · intro h; simpa using translate_las p h
  · intro h; simpa using translate_las (-p) h

end CBFIndependence
