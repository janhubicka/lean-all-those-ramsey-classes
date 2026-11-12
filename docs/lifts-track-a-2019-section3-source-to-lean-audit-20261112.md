# Original 2019 Section 3: Track A source-to-Lean proof audit

**12 November 2026 — independent source-contract review.**
This compares the numbered, frozen 2019 [`ramsey.tex`](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/ramsey.tex)
with the maintained, kernel-checked Lean source in this repository.
It makes no textual change to the printed manuscript and restores no
collaborator-removed TODO. References to a printed proof step describe
what the historical prose *asserts*, not an unrestricted Lean theorem.

## Source argument, in its original order

The printed
[`lem:amalgamationstr`](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/ramsey.tex#L2250-L2256)
seeks strong free amalgamation of two maximal forbidden-class witnesses
over their common shadow. Its proof, around
[`lemma:flip` and Claims 1–2](https://github.com/janhubicka/All-those-Ramsey-classes/blob/main/ramsey.tex#L2260-L2345),
first chooses a forbidden EHN witness to the full free amalgam,
then minimizes its **A-exclusive SOURCE vertex count**, and uses
genuine geometric pieces, flips and further separators to eliminate
the remaining B-exclusive part.

| Printed proof obligation | Exact maintained Lean status | Limitation |
| --- | --- | --- |
| Choose an injective forbidden EHN map into the SAME target from closure under HE-images | **Not valid in general.** `fiveCycleImageFamily_counterexample_to_blanketInjectivization` (`Lifts/EHNFiveCycleNoInjectiveReplacement.lean`) is verified; see Track D audit. | A tuple-surjective weak image need not fully embed in the target. |
| A flip exists for an actual chosen inner geometric source piece | **Conditional verified:** `geometric_actualGlobalWitness_selectedFlip_withSelection`, [PR #994](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/994); needs the original INNER global canonical relation in the opposite witness and matching root coordinates. | The inner relation implies inner-root injectivity; it is not produced from arbitrary collapsed images. |
| Rebuild a genuine older nested geometric piece after that SAME selected Q and full native forbidden source replacement | **Verified:** `nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier` and `nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol_withExterior`, [PR #1013](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1013). | Component nesting and an actual selected replacement are inputs; no universal positive-rank successor. |
| Preserve original old outer GLOBAL source symbol, whole outer carrier, ordered root image and exterior counts | **Verified:** the #1013 theorem preserves the same witness and equality of **SOURCE-vertex** counts outside the genuine outer piece for EVERY target subset. | Exterior conservation alone neither strictly decreases interior B rank nor yields the terminal A-minimizer contradiction. |
| Preserve the ORIGINAL target outer global relation | **Exact criterion verified:** `geometricGlobalCanonicalRelation_iff_rootInjective_of_weak` ([PR #1036](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1036)); its truth is equivalent to injectivity of the ordered root image under the given EHN map. | A colliding tuple makes that original relation false, even if the source symbol survives. |
| Compare the target outer relation before and after the SAME selected source replacement | **Verified:** `nestedGeometric_actualGlobalWitness_outerTargetRelation_iff_withExterior` ([PR #1055](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1055), [exact-head CI 43271200848](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/43271200848)). | This is preservation of **truth value**. In a collision both relation propositions are FALSE; it is not a root repair. |
| Iterate Claim 2 to eliminate all B-only private SOURCE vertices, then use original A-minimality | **Not established without further hypotheses.** Track C's local alternatives include a flippable piece, a smaller positive root, and an actual weak seam collision; exterior counts and one-step A-anchor maintenance do not discharge all branches. | Requires proof of eligibility at every positive state or a new treatment of the obstruction branches, plus the terminal step. |
| Derive unrestricted strong AP of the original maximal-lift age | **Open.** The source geometry and relation-truth lemmas do not establish a full maximal-common-lift forbidden-source exclusion. | Do not label `lem:amalgamationstr` or the resulting unrestricted Section 3 theorem verified. |

## Why source-symbol equality cannot replace target-root injectivity

The ORIGINAL global lift relation is indexed by an entire
positive-width rooted-piece equivalence class and is interpreted
only on tuples with **distinct** coordinates. Let `d` be a
genuine forbidden geometric piece and `f` an actual weak EHN map.
The exact verified criterion is

```text
originalGlobalRelation(Target, symbol(d), f ∘ roots(d))
  ↔ Injective(f ∘ roots(d)).
```

For a selected-Q flip, Track A preserves both `symbol(d)` and
`f ∘ roots(d)`, so the original target relation has the SAME
truth value before and after the replacement. This is compatible
with both being false. An assertion of a NEW TRUE target relation
requires an independent injectivity argument or different semantics;
source-root distinctness alone does not suffice.

## Separation of remaining tasks

* **Track A:** genuine nested source construction, exact carrier,
  original global source-symbol, target-coordinate and all-target
  exterior SOURCE-support conservation are verified; its latest
  target-truth interface is verified and merged.
* **Track B/C:** one eligible strict B-exclusive SOURCE descent and
  all exterior counts are formalized under their actual hypotheses.
  Universal successor selection and termination against the ORIGINAL
  A-source minimizer still require closing the smaller-root and
  collision alternatives, with state validity tracked between steps.
* **Track D:** maximal-common-lift treatment of weak-image defects
  and collisions is not proved by blanket HE-image closure. The
  collision counterexample targets the invalid shortcut, **not**
  the desired strong AP statement.
* **Track F / final application:** no unconditional maximal-lift
  shadow-avoidance or general strong amalgamation theorem follows
  from the conditional source-level flip geometry.

The audit intentionally adds **no new theorem**, no duplicate source
flip, and no automatic weakening of the printed statement. It
documents verified exported APIs and exact remaining dependencies.
