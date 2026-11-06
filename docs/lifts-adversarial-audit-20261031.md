# Adversarial audit: original functional lifting section (31 October 2026)

**Repository baseline:** `6c7b5d29362e335a033ebc6bfb74cb2ebc32a85b`. **Scope:** the 2019 Section 3
`lemma:flip`, Claims 1--2, `lem:amalgamationstr`, and maximal-lift
strong amalgamation. The original canonical lift uses **distinct** root
coordinates; auxiliary folded-root results are not a substitute.

## Exact certified/conditional boundaries

| Lean endpoint | What it proves | What it does not supply |
| --- | --- | --- |
| `OriginalClaim2InputCoveredOneStep.exists_injectiveLeftMinimizer_and_strictRightReplacement` | Under image closure AND full irreducible function-input-test coverage, there is a genuinely injective **left-minimal** forbidden witness with an actual strict **right-support** replacement. | The replacement may increase left support; no Claim 2 contradiction or unrestricted injectivization. |
| `FullFreeAmalgamOuterOldRootCriterion.finite_outerOldRoot_hasGeometricPiece_of_oppositeBoundary` | A transported old root yields an actual new geometric piece once exterior and **opposite interior** generated boundaries are exactly the old root. | The interior boundary equality is still a HYPOTHESIS, not a result of an arbitrary nested flip. |
| `InnerComponentOuterCutTransport.minimalInnerPiece_survivesOuterCut_withWholeGeneratedRoot` | The inner component and every generated inner-root vertex outside the old cut are in one outer-cut component, assuming inner component disjointness from the outer cut. | Other retained old interior vertices need not have been attached; full outer component and complete boundary remain to establish. |
| `ActualNestedFunctionalProfileCongruence.forbiddenNestedActualSource_iff_of_inner_profile_equiv` | Incompatibility truth is invariant under inner equivalent-piece replacement GIVEN both full nested diagrams and embeddings. | It does not construct the substituted full diagrams, or show the transported context is a minimal-separator piece with the old root. |
| `GlobalMaximalTraceConditionalStrongAmalgamation.globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree` | A genuine strong amalgam follows from explicit `GlobalCanonicalShadowFreeAmalgamation`. | That hypothesis is the global shadow-avoidance obligation, not proved for arbitrary connected HE-image-closed families. |
| `GlobalShadowAvoidanceFromGeometricConditions.globalCanonicalShadowFree_of_minimalGeometricConditions` | Proves shadow avoidance from `GlobalMinimalWitnessGeometricConditions`. | The geometric condition, including root test coverage and smallest-piece boundary matching, is an ADDITIONAL assumption. |

The exact proposition matters: `#print axioms` certifies a declaration **with
its hypotheses**; it never discharges those hypotheses. Keep the theorem
statements available for direct import, but do not advertise an unrestricted
Section 3 strong amalgamation result.

## Adversarial source-vs-paper findings

1. The proof's blanket “HE-image closure, hence assume f injective” is not
   valid for arbitrary weak maps. A target image of an EHN map can fail to
   be function-closed for arity two. The existing conditional closed-image
   factorization is correct under `FunctionInputTuplesCoveredByIrreducibleTests`.
   The nonempty unary/constant-function special case is covered; the printed
   arbitrary-arity hypothesis does not imply this extra condition.
2. The printed Claim 2 speaks of flipping the mixed `P'`; what is justified
   is flipping a **proper B-only sub-piece of P'**. Each iteration must preserve
   the chosen outer root, its entire generated boundary, its full rooted
   incompatibility profile, and the local B-only SOURCE count.
3. A one-step decrease of B-only SOURCE support is not a contradiction to
   the chosen minimum of A-only SOURCE support; the latter may increase.
   A finite contextual normalization plus a final A-to-B flip is still needed.
4. The nested profile theorem is not circular, but it is CONDITIONAL ON the
   two original full-functional nested free diagrams. The proof must supply
   these from a literal flipped source, not from a merely closed vertex context.
   Complete function fibres, possibly intersecting inner and outer interfaces,
   and test compatibility must be checked.
5. The exact old-root criterion still requires the *opposite* component's
   generated boundary equality. Establish a path-rerouting lemma that connects
   every retained old interior vertex to the transported inner component,
   then prove the boundary equality; do not apply nested-cut monotonicity
   when the old and inner cuts are incomparable.
6. Strong amalgamation of the maximal trace age is already constructed
   only **if** original-shadow forbidden avoidance is supplied. Neither
   regularity/precompactness nor the finite trace representation resolves
   this missing forbidden-avoidance lemma.

## Cleanup and verification policy

The active inventory currently protects research endpoints individually.
Thirteen source-level **transitively redundant root-marker files** are removed
in the accompanying cleanup commit: each named module is still imported by
another retained, independently protected lift endpoint. No Lean theorem
module, axiom-check endpoint, or historical counterexample was deleted.
The cleanup plan now reports redundant markers and their importing roots.
Do not delete an actual Lean file solely because it is absent from the public
API or has no incoming import; independently validated endpoints are often
standalone. A genuine dead-end removal needs import closure AND mathematical
ownership review.

CI compiles **every** `.lean` under `AllThoseRamseyClasses`, runs all
`CheckAxioms*.lean` and the existing no-admissions check. A new static
source-contract regression check flags unreviewed removal of six explicit
hypotheses. This is a guardrail, not a substitute for Lean kernel checking
or a new proof. The most recent completed main-branch CI at the baseline
was successful at `f827ceee...`; the newer `6c7b5d...` run was
in progress when audited.

## Next genuine Lean theorem targets

1. **Actual nested-flip interior component:** build the retained-old-interior
   path rerouting in the *new* source across incomparable function-closed cuts.
   Target both exact component equality and `Cl(N(C))=R`, or a precisely
   weaker sufficient hypothesis if full equality is false.
2. **Source-geometric contextual profile:** construct actual full nested
   diagrams and apply `forbiddenNestedActualSource_iff_of_inner_profile_equiv`
   without assuming the target conclusion; transfer all rooted tests.
3. **Iterated local support:** prove a finite decreasing measure of B-only
   SOURCE vertices inside a transported outer piece, preserving the original
   root coordinates, and then the final A-support contradiction.
4. **Root collision:** either derive the necessary injection from the
   actual maximal-common-lift setting or replace the printed one-step
   argument with an honest collision-tolerant alternative while checking
   precompactness for unbounded widths.

**Editorial contract:** the numbered `ramsey.tex` is frozen.
The matching separate manuscript `validation-todos.tex` receives new
review-only TODOs. No theorem label is promoted to green here.


## 1 November 2026 — Track B revalidation (new results; original audit retained)

The original 31 October description is a *historical baseline*. Its
source-level contextual-profile gap is now substantially closed:

- Merged [#741](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/741)
  constructs the **named full native** old/new contextual diagrams,
  their full original-side embeddings, and the outer-to-nested
  forbidden-test decomposition. Merged [#746](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/746)
  proves inverse full functional reassociation and nested all-test
  invariance. Both are CI/axiom-audited.
- Merged [#750](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/750)
  proves `functionalActualContext_profile_equiv_of_inner_equiv`:
  replacing a profile-equivalent inner full root extension inside
  **chosen actual full functional** amalgams preserves all forbidden
  tests at any outer full root embedded in the retained side.
  No nesting of cuts, isomorphism closure of the forbidden family,
  or weak-map injection is assumed.
- Merged [#752](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/752)
  embeds the **full old outer root** in the retained complement
  under exact root survival; merged [#754](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/754)
  identifies the OLD contextual vertex set with the actual old
  geometric outer piece, assuming the complete inner component
  and root are inside that piece.
- Merged [#753](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/753)
  constructs the ACTUAL old/new induced functional contexts and
  their entire all-test profile equivalence with exact root
  coordinates. Merged [#758](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/758)
  identifies the profiles of equal closed induced carriers through
  an onto full rooted isomorphism.
- Merged, fully CI-checked [#767](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/767)
  proves `geometricOriginalPiece_profile_equiv_transportContext`.
  Under inclusion of the entire selected inner piece in the old outer
  geometric piece, outer-root survival, inner all-test equivalence
  and a literal full new source amalgam, the **genuine original
  geometric piece** and the **actual new closed source context**
  have exactly the same complete forbidden test profile and ordered
  full root coordinates. The merge commit changed only the new
  theorem, its axiom test and its protected active root.

**What is still open:** The new closed context is NOT automatically a
single component adjoining a minimal separating closed root. Prove the
whole new opposite component, the equality of its **complete
function-generated neighbourhood boundary** with the old full root,
and that the context equals that component plus the root. Even then,
identifying the resulting global quotient symbol must compare the
entire ordered *functional root structures*, not just the tuple.
Merged, fully axiom-audited [#776](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/776)
and [#781](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/781)
now prove the complete native functional root-structure identity
under identical FULL root maps and the true selected GLOBAL quotient
index transfer under identical all-test fixed-root profiles. Merged
[#788](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/788)
recovers a genuine geometric piece with the PRESCRIBED ordered old
root when both generated boundary equations and the exact
single-component context identity are supplied. Draft [#795](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/795)
and stacked [#796](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/796)
are the final conditional global-symbol compositions; their full
CI must pass before they are declared validated. Neither supplies
the still-open arbitrary nested-flip opposite-boundary geometry.

This finishes **Track B's actual contextual incompatibility-profile
congruence**, not the unrestricted paper's Claim 2, root-injectivity
repair, terminating B-only-source flip sequence, shadow avoidance or
the strong-amalgamation conclusion. Original numbered manuscript prose
remains frozen; the separate ATRC-069 review-only TODO records the
remaining boundary obligation.


## 3 November 2026 — completed conditional GLOBAL symbol endgame

Fully CI-verified, merged [#795](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/795)
proves `geometricFlip_preserves_globalPieceSymbol_of_newGeometricContext`:
if an actual finite forbidden-source inner replacement preserves the
original ordered outer root and its new context is literally the vertex
set of a NEW genuine geometric minimal-separator piece, the two selected
pieces determine the **same original 2019 GLOBAL piece symbol**.
The proof compares complete functional root structures, ALL native
incompatibility tests, and the actual global quotient; no weak target
map is assumed injective.

Merged, fully audited [#796](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/796)
proves `geometricFlip_globalPieceSymbol_of_exactOppositeBoundaries`:
it CONSTRUCTS that new geometric piece on the original Fin n root
when there are two separated new outside-old-root components,
the **complete function-generated boundary of each is the old root**,
and the transported context equals that root plus one entire
component. It also derives full root closedness and source injectivity
from the original complement's native full embedding, rather than
postulating those separately.

**Unresolved for unrestricted Claim 2:** The hypotheses identifying the
actual new outer component, the opposite entire generated boundary,
and the exact context carrier are not supplied automatically by the
algebraic endgame. Track A owns their proof in the actual nested
source flip; Track C must still provide the terminating B-only
source-support descent and final A-minimality contradiction. There
is also the separate issue of colliding target root images (ATRC-068).

Draft [#819](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/819)
studies the resulting ORIGINAL global outer-piece relation in the
actual weak-image target, keeping target-root injectivity explicit.
Draft [#827](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/827)
derives finiteness of selected literal new source flips from their
genuine finite forbidden witnesses. Both are UNVERIFIED until final
CI/axiom checks succeed. The frozen numbered manuscript has not
been rewritten; review TODOs remain open for the missing hypotheses.


## 4 November 2026 — genuine nested Track A proof chain (CI boundary)

The October audit above is a historical record. The following original
native source-geometry results are now **merged with successful CI**:

- [#805](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/805):
  the exact genuinely selected canonical replacement Q has a private
  connected component generating the entire full functional root.
- [#811](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/811):
  the same literal replacement source has a genuine inner geometric
  minimal-separator piece.
- [#822](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/822),
  [#826](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/826),
  [#830](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/830)
  and [#834](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/834):
  source-native incomparable-cut attachment, complete older opposite
  boundary and conditional new older minimal-separator reconstruction.
- [#839](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/839):
  in the actual nested original geometric source, the opposite older
  exterior avoids the entire inner gluing root and selected component.
  Its latest version also derives full inner-piece containment and
  survival of the complete older root coordinates.
- [#862](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/862):
  merged 4 November after successful CI; under *one* actual component
  nesting premise, the genuine original outer piece has the same
  all-test rooted forbidden diagram profile as the actual transported
  closed context, with the correct ordered old root coordinates.

**New draft, not yet kernel-validated:** The source-side next steps are
split into exact proof obligations, rather than silently packaged into
a purported unrestricted result.

1. [#866](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/866)
   reflects the preserved opposite older exterior's exact entire
   generated boundary back into the unchanged full native complement.
   It also derives the closed preimage of the older root and privacy
   of the complete complementary exterior component. Its first CI
   uncovered a tactic rewrite-direction error; the repair was pushed
   and a new CI run queued.
2. [#876](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/876),
   stacked on #866, combines that exterior with the separately proven
   new Q-side older boundary to construct an actual new older
   geometric minimal-separator piece. The only extra new-side
   hypothesis is a Q-private component with its complete generated
   inner root (which #805 supplies for a genuinely selected Q).
3. [#879](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/879),
   stacked on #876, uses the genuinely selected canonical Q witness,
   merged source-finiteness result #827 and literal F-membership of
   New to remove that Q-boundary and new-source-finiteness hypothesis.
   It packages the resulting new older piece as an actual forbidden
   geometric piece.
4. [#881](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/881),
   independent of the boundary chain, proves that **all** Q-private
   vertices lie in one root-complement component. The previously
   proved complete generated root equation for *some* Q-component
   does not imply this for arbitrary rooted extensions; the actual
   geometrically selected source and its FULL rooted isomorphism do.

**Remaining Track A bridge (do not mark validated):**
Prove the exact equality of vertex sets

  NewContext = transportedOlderRoot ∪
    component(New minus transportedOlderRoot, selectedInsertedQVertex)

for the **actual** selected Q and literal retained complement.
This requires transferring every retained private old-context vertex
through the two full free-amalgam diagrams (the merged #793 membership
equivalence), attaching all Q-private vertices (the #881 component
lemma), and treating surviving inner-root vertices that may lie
outside the older root. The new geometric piece must have the
**correct selected orientation** (inner new component, not the
opposite retained exterior), and its entire ordered native functional
root must agree with the rooted closed context before #795/#796
transfers the GLOBAL canonical piece symbol.

Do not infer this carrier identity merely from generated-boundary
equalities. Do not confuse source vertices with potentially colliding
weak target-map images. Root collision and the positive-local-B-support
successor / terminating support descent are still separate obligations.
The numbered 2019 manuscript remains frozen; this ledger is
review-only documentation.
