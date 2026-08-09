# Axiom audit

This document records the kernel dependency audit for the stronger common
fixed-point theorem. The public theorem applies to commuting continuous
self-maps of `[0,1]` that are weakly monotone on the cells of finite
partitions; it has no definability or o-minimality hypothesis.

## Exact kernel result

Last reproduced on 2026-08-09 after the clean 3,329-job project build and
again before the final manuscript release.

Lean reports the same dependency set for each of the following declarations:

- `CommutingInterval.PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point`
- `CommutingInterval.finitePiecePL_common_fixed_point`
- `CommutingInterval.finitePieceMonotone_common_fixed_point`

For each declaration, `#print axioms` returns exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean's standard propositional-extensionality, classical-choice, and
quotient-soundness foundations. There is no `sorryAx` and no project-defined
axiom in any of the three dependency sets.

To reproduce the audit without retaining a nondependency source module, create
a temporary Lean file containing:

```lean
import CommutingInterval

#print axioms CommutingInterval.PiecewiseLinearCorrectedAssembly.finitePiecePL_common_fixed_point
#print axioms CommutingInterval.finitePiecePL_common_fixed_point
#print axioms CommutingInterval.finitePieceMonotone_common_fixed_point
```

Run it with `lake env lean`, then remove the temporary file. The audit recorded
above was rerun this way after the source-pruning rebuild.

## Clean stronger import closure

The package root `CommutingInterval.lean` imports
`CommutingInterval.PiecewiseMonotoneMain`. That module uses the corrected
namespaced piecewise-linear assembly, whose Boundary 6, Boundary 9, and
Boundary 10 implementations are fully proved. A recursive scan of this
40-module transitive project closure contains no executable `sorry`, `admit`,
or project `axiom` declaration. All Lean sources outside that closure were
removed, so the entire remaining Lean tree is exactly this audited closure.
The obsolete tame/o-minimal infrastructure was removed as well.
