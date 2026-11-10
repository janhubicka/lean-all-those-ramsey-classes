# Track A closeout: genuine nested functional flip geometry

**8 November 2026.** This is an audit record for the original 2019
Section 3 lifting argument. The numbered `ramsey.tex` remains **frozen**;
do not revive TODOs that collaborators removed or commented out.

> **10 November verified-status update.** Track A source geometry
> and its proof consolidation are merged after independent successful
> exact-head Lean CI: [#964](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/964),
> [#968](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/968)
> and [#972](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/972).
> The strengthened same-Q concrete step with exterior SOURCE counts
> preserved for arbitrary target subsets is itself verified in
> [#948](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/948).
> Historical draft entries below describe the stages before those merges.
> The unrestricted printed Claim 2 and strong AP are **not** validated.

## What is proved

The `Track A` task is the **source-geometric** part of the nested flip.
For two actual geometric pieces of one finite forbidden native functional
source, assume only nesting of the selected components (not inclusion
of their full closed roots). For the **same genuinely selected** canonical
inner replacement `Q`, with a literal full native free-amalgam source
`New = Q +_U Complement` that remains forbidden:

1. The opposite exterior survives, with the exact *generated* full
   native boundary; the selected Q-private side is connected outside
   its entire root. These are derived from the actual selected-piece
   hypotheses, not postulated as generic boundary axioms.
2. The new whole outer-cut component plus the transported older root
   equals the **actual transported closed outer context as a vertex set**.
3. A genuine new minimal-closed-separator outer piece exists, oriented
   towards the inserted Q side, with the **same ordered Fin m outer
   root coordinates**, without assuming the inner and outer cuts
   are comparable.
4. That actual piece has the **same original globally indexed canonical
   piece symbol** as the old outer piece, by equality of all full
   rooted native functional gluing tests, not just a graph profile.
5. The stronger core theorem also retains the **exact carrier
   equality**. Its earlier symbol-only API is a corollary. For a
   prescribed same-Q strict decrease of B-exclusive SOURCE vertices
   in the transported context, the strict decrease therefore holds
   on the **actual new outer geometric piece**.

The principal core API is
`nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol_withCarrier`
in `Lifts/NestedSelectedGlobalOuterPieceSymbol.lean` and the preserved
symbol-only API is
`nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol`.
The rank bridge is
`nestedGeometric_selectedFlip_strictLocalRank_on_newGeometricPiece`
in `Lifts/NestedSelectedOuterGeometricPieceLocalRank.lean`.
The selected right-to-left same-witness endpoint
`geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport`
lives in `Lifts/Claim2SelectedActualGeometricOuterStep.lean`.

## Previously verified PRs (exact individual Lean CI)

| PR | Main contribution | Completed successful Lean run |
| --- | --- | --- |
| [#899](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/899) | Actual older outer symbol and prescribed ordered root | [42317502369](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42317502369) |
| [#909](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/909) | Transfer to weak target under explicit **outer root-image injection** | [42317570035](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42317570035) |
| [#913](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/913) | Witness-level selected Q and original target outer relation | [42317618873](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42317618873) |
| [#921](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/921) and [#922](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/922) | Same selected Q returned with strict local B-source count | [42318953134](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42318953134) |
| [#925](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/925), [#927](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/927) | Same-Q actual component rank and retained carrier in geometric piece | [42426181402](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42426181402) |
| [#929](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/929) | Selected right-to-left actual source/outer-piece/rank step | [42426576246](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42426576246) |
| [#942](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/942), [#945](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/945), [#948](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/948) | Exact exterior SOURCE support for any target subset, promoted to one concrete selected-Q successor | [42479535174](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42479535174) |

The original Track A geometric proof consolidation is **merged and
exact-head CI-verified** as [#964](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/964)
([Lean run 42485106398](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42485106398)).
The stronger core theorem is defined once in its natural geometry
module; the symbol-only public theorem is its direct corollary.
No underlying proof or theorem statement is weakened.

## What Track A does NOT establish

- **Track C:** that every positive-rank valid Claim 2 state has the
  required flippable B-only inner piece; the complete iterated
  preserved-exterior invariant; terminal A-exclusive minimizer
  contradiction.
- **Track D:** that a weak EHN target map has distinct outer-root
  target coordinates. The target-level theorems explicitly assume
  injectivity; source-piece roots being injective is insufficient.
- **Full Section 3 / Track F:** unconditional global canonical
  shadow avoidance, maximal-lift strong amalgamation, and any
  unrestricted Claim 2 or Ramsey conclusion.

These are *independent mathematical gates*, not missing statements
in Track A geometry. A conditional theorem with verified Lean axioms
must not be reported as its unrestricted conclusion.

## Regression gate

The exact PR head must pass the repository's pinned Lean build,
the named `CheckAxiomsNestedSelectedGlobalOuterPieceSymbol.lean`,
`CheckAxiomsNestedSelectedOuterGeometricPieceLocalRank.lean`, and
`CheckAxiomsClaim2SelectedActualGeometricOuterStep.lean`, together
with the repository-wide permitted-axioms, no-admissions and active-root
inventory checks. Review the public theorem signatures after the move;
no theorem statement is intended to change.


## 9 November — additional concrete-step proof consolidation

The already verified `geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior`
from #948 strictly strengthens the old concrete step (#929): it
retains precisely the same actual selected Q, full forbidden native
source, complement map, original ordered outer root, global piece
symbol and strict B-only SOURCE-rank decrease, **and also** proves
that for every subset `TargetSet` of the target, the number of
SOURCE vertices outside the entire actual outer piece whose
images lie in `TargetSet` is unchanged.

The resulting cleanup is **merged and verified** in
[#968](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/968)
([Lean run 42664353844](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42664353844)).
It relocates the stronger implementation into
`Lifts/Claim2SelectedActualGeometricOuterStep.lean` and retains
the older theorem as a direct corollary. The historical
`Lifts/Claim2SelectedActualGeometricOuterStepExterior.lean`
continues as a backwards-compatible import. Both signatures and
separate axiom checks are retained. This was a **maintainability
refactor**, not a proof of existence of a positive-rank successor
or terminal Claim 2 contradiction. No numbered manuscript text changed.

## 10 November — adversarial shortening of the witness-level target conclusion

The extra original outer TARGET relation in
`nestedGeometric_actualGlobalWitness_preserves_outerRelation`
was previously obtained through a second nested source-symbol
transport argument. This is mathematically redundant: the INPUT
old forbidden source, weak map `f`, and the theorem's already
explicit outer target-root injectivity imply the relation directly
by `geometricGlobalCanonicalRelation_of_weak`. A cleanup branch
uses this direct proof and keeps the statement unchanged.
[Detailed audit](lifts-track-a-direct-target-relation-audit-20261110.md).

Draft [#969](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/969)
was closed unmerged for exactly this reason. Its extra conclusion
was not a new result, even though it compiled. The essential
Track A source-symbol preservation and Track C/D obstructions
remain exactly as stated above.

## 10 November — final validated Track A cleanup and boundaries

[#972](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/972)
is now **merged** following successful full exact-head
[Lean CI run 42820020880](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/42820020880).
It preserves the witness-level theorem statement but replaces its
unnecessary old-symbol target-relation transport with the direct
`geometricGlobalCanonicalRelation_of_weak` application on the
ORIGINAL forbidden source and old weak target map.
The actual source-flip construction remains unchanged.

This completes the originally assigned **Track A native source geometry
and its cleanup**. It proves genuine source-piece reconstruction and
preservation of the original indexed global piece **symbol** under a
specified selected-Q replacement, with an exact ordered full root and
native functional gluing tests. The later same-Q strict B-only SOURCE
rank/exterior invariants are valid one-step certificates subject to
the **explicit** hypotheses of an eligible selected inner piece.

**It does not prove the unrestricted printed Section 3 Claim 2.**
The still-independent obligations are Track C's eligible successor at
every positive state and terminal minimizer contradiction, Track D's
possible weak target-root collisions, and the full maximal-lift
shadow avoidance / strong amalgamation conclusion.

Historical intermediate draft labels elsewhere in this ledger remain
as records of the proof development and must not be interpreted as
the current merge or CI state. The numbered 2019 manuscript remains
frozen; never restore TODOs removed by collaborators.
