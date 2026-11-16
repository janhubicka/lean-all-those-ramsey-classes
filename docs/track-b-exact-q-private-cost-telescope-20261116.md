# Track B: exact A-source cost telescope for one-sided selected Q chains

**16 November 2026; stacked draft on #1250.** The frozen numbered
2019 manuscript and collaborator-removed TODOs remain unchanged.

The previous A-free selected-Q state relation stores one actual
forbidden selected rooted Q, its full native Q+old E free-amalgam,
the exact old E target-map coordinates, old inner A-freeness,
and a B-source-rank-decreasing new forbidden source/geometric state.
We previously established monotone total A-exclusive SOURCE
support and strictly decreasing total B-exclusive SOURCE support.

New `Claim2AFreeQPrivateCostTelescope.lean` strengthens this
quantitative interface without selecting a second Q or a
different source:
- `claim2NativeAFreeQStepWithPrivateCost` repeats the entire
  same-Q A-free native provenance certificate and **adds** the
  exact SOURCE count of private Q-nonroot vertices mapped into
  the A-exclusive target region *for the same chosen Q*.
- `claim2NativeAFreeQStep_existsPrivateCost` upgrades EVERY
  previous A-free native Q step to such a costed step.
- `claim2NativeAFreeQStepWithPrivateCost_exactTotalA` invokes
  the merged Track C exact full-native Q+E source cardinality
  identity: `A_total(new) = A_total(old) + privateA(Q)`.
- `Claim2NativeAFreeQCostedChain` is an inductive finite chain
  whose EACH edge retains its exact private selected-Q
  source cost, rather than attaching an arbitrary list
  of unrelated natural numbers to the endpoint.
- Theorems establish projection to the previously checked
  A-free Q-step chain, existence of a matching costed chain
  for any existing chain, and exact telescoping
  `A_total(terminal) = A_total(initial) + totalPrivateQCost`.
  Independently the SAME chain retains strict B-source
  rank budget `steps + B_total(terminal) ≤ B_total(initial)`.

This exact additive A-cost is useful for assessing potential
weighted or amortized descent methods, without claiming one
exists. Note the opposite monotonicity: A increases by
nonnegative private-Q costs while B decreases. The original
A-minimal or (A,B)-lex-minimal weak EHN witness need NOT remain
globally minimal after a selected-Q replacement; applying the
original extremal smaller-root theorem to a later witness
would require an additional argument.

This is a CONDITIONAL chain identity. It does not eliminate
initial source-test/root collisions, smaller-root capture or
A-mixedness, nor establish unrestricted original Claim 2 or
general strong amalgamation. No weak-map image quotient.

Named `#print axioms`, protected source root and full exact-head
Lean/allowed-axiom/no-admission/import/source-contract/inventory
CI are required before merging. Source without admissions
is not a substitute for kernel compilation.
