import CBFIndependence.PairIndependence
import CBFIndependence.GeometryContinuationAudit

/-!
# Checking the CBF independence theorem

Open `CBFIndependence/Statement.lean` for the mathematical definitions and statements.
Run `lake build` from the project directory to check the proofs below with the
Lean and mathlib versions pinned in this project.
-/

namespace CBFIndependence

universe u v

example : OptimizerWellposedStatement.{u,v} := @common_local_wellposed
example : LocalActivityStatement.{u,v} := @Barrier.local_normal_equation
example : BoundaryReductionStatement.{u} := @boundary_las_at
example : CBFIndependenceStatement.{u,v} := undesirable_equilibrium_las_pair_independent

#print axioms undesirable_equilibrium_las_pair_independent

end CBFIndependence
