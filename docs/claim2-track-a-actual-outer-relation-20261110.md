# Track A/C: same-Q genuine outer relation at the original target root

**10 November 2026 — proposed proof; not kernel-verified until exact-head Lean CI.**

The merged stronger original 2019 right-to-left selected inner replacement
`geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior`
returns the **same** genuine Q, literal full native forbidden New,
weak target map, new actual older geometric piece, old ordered root and
GLOBAL original piece class symbol, strictly smaller B-only SOURCE count,
and equality of all outside-outer-piece SOURCE counts.

The additional source-to-TARGET relation endpoint is
`geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior_andOldRelation`
in `Lifts/Claim2SelectedActualOuterRelation.lean`.

Its extra input is ONLY the explicit target-image injectivity of
the original outer ordered root:

```lean
hOuterRootTargetInjective :
  Function.Injective (fun i : Fin n => f (outer.roots i))
```

It transports this injectivity to the exact new roots by their unchanged
target coordinates. The verified
`geometricGlobalCanonicalRelation_of_weak` realizes the new globally
indexed piece relation. The verified original symbol equality identifies
the classes of the old/new selected patterns in the original functional
global quotient. Applying `globalFunctionalCanonicalRelation_iff`
then transports the SAME realization to the old symbol (not to an
auxiliary folded symbol) on the original target root tuple.

## Audit boundaries

* Both source geometry and target relation refer to ONE selected Q/flip.
* The target map is a **weak HE**, not assumed globally injective.
* The **OUTER** root target-image injectivity is explicitly added;
  the existing **INNER** root target-image injectivity is a
  different input, and neither implies the other.
* No new forbidden-image closure, no quotient of target images,
  no new blanket `F`-isomorphism closure, no root cut inclusion.
* This is not the general existence of a flippable inner B-only
  piece in every positive-rank state (Track C), a terminal minimizer
  contradiction (Track C), or a solution of outer target collisions
  (Track D).

**Validation gate:** exact-PR-head full pinned Lean compilation,
`CheckAxiomsClaim2SelectedActualOuterRelation.lean`, no admissions,
permitted axioms, source-contract audit, active root inventory. Preserve
frozen numbered `ramsey.tex` and collaborators' removed TODOs.
