# Track A closeout: genuine nested functional flip geometry

**8 November 2026.** This is an audit record for the original 2019
Section 3 lifting argument. The numbered `ramsey.tex` remains **frozen**;
do not revive TODOs that collaborators removed or commented out.

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

The current cleanup moves the proof of the strengthened core theorem
from the rank module into its natural geometry module. The original
symbol-only theorem now follows by dropping one conjunct; no proof is
weakened and no independent geometric proof is duplicated. **Verify
this refactor at its own exact PR head before calling the cleanup green.**

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
