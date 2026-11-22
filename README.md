# CBF-pair independence of local asymptotic stability

Open [CBFIndependence/Statement.lean](CBFIndependence/Statement.lean) to review the assumptions, the three optimization problems, the meaning of stability for all maximal solutions, and the equivalences for the ambient, boundary, and safe-initial-state problems. The main statement is `CBFIndependence.CBFIndependenceStatement`.


With Lean's `elan` toolchain manager installed, run the following commands from this directory. The project pins Lean and mathlib to 4.24.0. The first command retrieves mathlib's compiled dependencies.

```sh
lake exe cache get
lake build
```

The default build checks the proof of `CBFIndependence.undesirable_equilibrium_las_pair_independent` against the main statement. It also checks the separate optimizer, local activity, and boundary reduction results against the statements in the same file, and prints the axioms used by the main theorem.
