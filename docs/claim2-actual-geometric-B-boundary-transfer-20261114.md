# Track B/C — actual geometric selected-Q boundary transfer

**14 November 2026 — exact-source interface, pending full Lean CI.**

The verified parent theorems are `fullNativeReplacement_pieceScoped_activeBoundaryInj_transfer`
and `claim2_outerBActiveBoundaryInjection_restrict_to_retainedComplement`.
Their generic assumptions do not, by themselves, show that an actual
genuine selected-Q source replacement preserves the local B-boundary
invariant needed to iterate positive-rank Claim 2.

This module specializes both to the ORIGINAL full native source
free-amalgam diagram of a chosen inner geometric piece `inner`
of `Old`, using `geometricGlobalSource_freeDiagram Old inner`.
Its retained side is the LITERAL complete old complement embedding,
not a selected isomorphic copy.

The new outer carrier identity returned by the actual selected-Q
construction is

```lean
iQ '' univ ∪
  iE '' (oldOuterContextInInnerComplement Old outer inner)
    = geometricPieceVertices New newOuter
```

By definition `oldOuterContextInInnerComplement` is exactly the
preimage of the OLD outer carrier under the old complete
complement embedding. This discharges the generic subset hypothesis
of the piece-scoped transfer, not by any target-quotient trick.
The inner-root seam condition gives the exact root-seam hypothesis
of the new/old common-root source diagram, while the restriction
theorem turns the old P-scoped active boundary injection into
precisely the OLD retained-complement input.

If the SAME selected Q also has the verified no-new-B witness,
the conclusion gives `Set.InjOn flip` on the ENTIRE function-generated
boundary of any new B-exclusive source vertex in the reconstructed
new geometric outer carrier. Full new common-seam injection is
NOT required and collisions at Q-only non-active boundary vertices
may persist.

## What is and is not discharged

This directly discharges the old-source free-diagram and carrier
preimage obligations for one selected-Q ACTUAL geometric successor.
The theorem still accepts the concrete hNewFree, hCarrier, hSameE
and hNoNewB outputs explicitly; these are returned by the selected-Q
same-witness theorem, and still need to be destructured and
composed with this lemma in the final real successor theorem.

The initial B-active boundary injection of a minimal selected outer
piece is NOT established. Neither are smaller-root A-mixed/old-root
capture obstructions, terminal outer-root target-image injection
from source-symbol equality, or the original minimality contradiction.

No original 2019 manuscript/tex edit. Avoid re-adding author-removed
TODO notes.

## Verification gate

This is a new proposed theorem, not yet kernel-verified. Require
exact-head full Lake/Lean build, named `#print axioms`,
active-root/source-integrity, permitted-axiom inventory,
original Section 3 contracts, and no-admissions before merge.
