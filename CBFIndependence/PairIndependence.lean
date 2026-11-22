import CBFIndependence.LocalWellposed
import CBFIndependence.BoundaryLAS

namespace CBFIndependence
open Set Metric Filter Topology
noncomputable section

/-- CBF-pair independence with the affine plant, optimization program and two
barriers as its inputs. Strong convexity is pointwise in the state. Slater is
required at the distinguished point only. There is no boundary, regular-zero,
optimizer-continuity, local-activity, flow-uniqueness or stability premise. -/
theorem undesirable_equilibrium_las_pair_independent.{u,v} : CBFIndependenceStatement.{u,v} := by
  intro E W _ _ _ _ _ _ U q oU S H J A P p sameH sameJ sH sJ eqH nom
  obtain ⟨bd,zH,zJ,nH,nJ,eJ,_,_⟩ := equilibrium_and_activity oU S H J A P p sameH sameJ sH sJ eqH nom
  obtain ⟨O,oO,pO,OU,well,bH,bJ,eq⟩ := common_local_wellposed_dynamics oU S H J A P p sameH sameJ sH sJ eqH nom
  obtain ⟨r,hr,ballO⟩ := Metric.mem_nhds_iff.mp (oO.mem_nhds pO)
  let V := ball (p:E) (r/2)
  let Q := closedBall (p:E) (r/2)
  have VQ : V ⊆ Q := ball_subset_closedBall
  have QO : Q ⊆ O := (closedBall_subset_ball (half_lt_self hr)).trans ballO
  have VO := VQ.trans QO
  have pV : (p:E) ∈ V := mem_ball_self (half_pos hr)
  have equal := eq.mono (inter_subset_inter_left (frontier S) VO)
  have one (K : Barrier U) (z : K.h p = 0) (same : ∀ x ∈ U, 0 ≤ K.h x ↔ x ∈ S)
      (bk : BarrierDynamics (ambientField (K.field oU A P)) K.h (K.α ∘ K.h) O S) :
      let F := ambientField (K.field oU A P)
      (StrongLAS (MaximalSolutionsOn F V) (p:E) ↔ StrongLAS (MaximalSolutionsOn F (V ∩ frontier S)) p) ∧
      (StrongLAS (MaximalSolutionsOn F V) (p:E) ↔ StrongLAS (MaximalSolutionsFromOn F V S) p) := by
    let F := ambientField (K.field oU A P)
    have dh (x : E) (hx : x ∈ V) := (K.deriv_at oU ⟨x,OU (VO hx)⟩).differentiableAt
    have act (x : E) (hx : x ∈ V) := bk.active x (VO hx)
    have sign x (hx : x ∈ V) : 0 ≤ K.h x * K.α (K.h x) := by
      by_cases h : K.h x = 0
      · simp [h]
      · exact (K.restoring _ (K.range_ok (OU (VO hx))) h).le
    have red := boundary_las_at (F := F) (V := V) (Q := Q) (p := (p:E)) (ρ := K.ρ) isOpen_ball pV
      (isCompact_closedBall _ _) VQ (K.smooth.continuousOn.mono (QO.trans OU)) z isClosed_frontier
      (fun x hx => bk.zero_iff x (VO hx)) (bk.continuous.mono VO) dh act
      (fun x hx => K.range_ok (OU (VO hx))) K.cont K.restoring
    refine ⟨red,fun full => full.mono (fun c hc => hc.1),fun safe => red.mpr (safe.mono ?_)⟩
    have sub : MaximalSolutionsOn F (V ∩ frontier S) ⊆ MaximalSolutionsOn F V :=
      maximalOn_inter_subset (fun c hs hz t ht => (bk.zero_iff _ (VO (hs.2 t ht))).mp
        ((normal_sublevel_invariance dh act sign hs).1 t ht ((bk.zero_iff _ (VO (hs.2 0 c.zero_inDomain))).mpr hz)))
    intro c hc
    have init := hc.1.2 0 c.zero_inDomain
    exact ⟨sub hc, (same _ (OU (VO init.1))).mp ((bk.zero_iff _ (VO init.1)).mpr init.2).ge⟩
  obtain ⟨oneH,safeH⟩ := one H zH sameH bH
  obtain ⟨oneJ,safeJ⟩ := one J zJ sameJ bJ
  rw [← maximalOn_eq_of_eqOn equal] at oneJ
  exact ⟨bd,zH,zJ,nH,nJ,eJ,V,isOpen_ball,pV,VO.trans OU,well.mono VO,bH.mono VO,bJ.mono VO,
    equal,oneH.trans oneJ.symm,oneH,oneJ,safeH,safeJ,
    fun x hx => exists_maximal_solution_on isOpen_ball (bH.continuous.mono VO) hx,
    fun x hx => exists_maximal_solution_on isOpen_ball (bJ.continuous.mono VO) hx⟩

end
end CBFIndependence
