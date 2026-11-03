# Track B: contextual equivalence for the original 2019 functional lift

**Status: in progress; not a proof of Claim 2 or Section 3 strong AP.**
Baseline: 1 November 2026, after #737/#738 were merged.
Owner: Track B (native functional diagrams and incompatibility-profile transport).
Other tracks work independently on paths/cuts (A), finite descent (C),
root-image collisions (D), the lift consequences (E/F).

## Exact missing inference

The paper's iteration replaces a proper B-only piece inside a larger
mixed forbidden-source piece. To apply the *outer* canonical lift symbol
again, it is necessary to preserve ALL of:

1. The entire ordered old outer root and its full native functional
   structure (not only its weak-map image).
2. A genuine new **geometric** minimal-separator piece on that root.
3. Its complete rooted incompatibility profile against **every** test,
   with full native relations and function fibres.
4. A strict B-only **source-vertex** count inside that piece (Track C).

These are logically distinct. `ActualNestedFunctionalProfileCongruence.lean`
already proves an actual forbidden-membership equivalence under matching
nested full native free-amalgam diagrams and image/isomorphism invariance.
It cannot construct those diagrams or the transported geometric cut.

## This PR's structural contribution

`NamedNestedFunctionalContext.lean` proves
`fullFreeAmalgam_nestedContext_namedFullDiagram`:

If `W = L +_H R` is a genuine full functional amalgam and
`S ⊆ R` is closed and includes the whole H-root, then the exact
induced context `K = iL(L) ∪ iR(S)` has a **named** full diagram

`W|K = L +_H (R|S)`.

The theorem constructs full embeddings of the old L, root H, and
exact induced R|S, whose underlying vertex maps agree with those
from W. All four free-amalgam fields (coverage, intersection,
relation tuples, *complete* function fibres) are part of the
statement. This strengthens the earlier anonymous induced-subtypes
diagram in `GlobalFlipContextInducedFreeDiagram.lean`.

`geometricOuterContext_has_namedFullDiagram` specializes the new
lemma to the old outer piece P, inner piece d, replacement rooted
piece Q, and the retained exact complement E. It requires only
the original inner roots to lie in P and the new full functional
gluing certificate. It **does not assume any profile conclusion**.

Both endpoints have individual `#print axioms` checks in
`CheckAxiomsLiftNamedNestedContext.lean`. **Do not mark verified
until the actual full Lean CI and permitted-axiom audit pass.**

## Next proof obligation: attaching an arbitrary test

Given the named `Q +_H E_P` context and an arbitrary rooted
outer test `T`, construct a literal *compatible* diagram of
`E_P` with T over the exact outer root. Verify in particular:

- The two-step gluing is genuinely **full** with compatible root
  embeddings, and can be reassociated to `Q +_H Ext` for a common
  `Ext` containing the actual retained right context and T.
- This construction works for **every** test in the definition of
  the incompatibility class, including higher-arity function fibres
  and non-injective weak EHN witness maps.
- When both old and replacement inner sources are decomposed against
  this **same** Ext, the existing
  `forbiddenNestedActualSource_iff_of_inner_profile_equiv`
  applies; use the full-diagram uniqueness theorem and forbidden
  family isomorphism closure to pass from existential to *chosen*
  sources.
- Finally, identify the transported context with a **geometric**
  outer piece. This last step depends on the opposite generated
  boundary equality under the inner flip (Track A); closure of
  `K` alone is insufficient.

Do not infer preservation of an outer incompatibility class directly
from closure or an abstract substitution theorem. For the old and
inner cuts, **no nesting is assumed**. Incomplete functional
relation/fibre reflection can invalidate the attempted reassociation.

## Manuscript

`ramsey.tex` is frozen. The existing review-only item **ATRC-069**
in the manuscript's `validation-todos.tex` already records this
gap. Add/adjust its validation status only after CI, and do not
repeat or promote it to a green proof marker. No prose has been changed.
