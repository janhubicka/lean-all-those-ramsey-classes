# Track B closing diagram for original 2019 Claim 2 (4 November 2026)

**Scope:** the exact FULL-native functional source replacement in Section 3
of *All Those Ramsey Classes* (2019), for incomparable inner and older
outer closed roots. Do not confuse this with the unrelated "Track B"
on the girth or BANANA projects.

**Status:** mathematical interface audit, not a proof of unrestricted
Claim 2. The original numbered manuscript `ramsey.tex` is frozen;
the existing ATRC-069 and ATRC-070 validation notes remain open.

## What is now fully certified on `main`

The following statements are distinct and have complete successful
project CI, kernel-axiom, source-contract, no-admissions and inventory
checks on their final merged heads.

| Obligation | Lean source | PR |
| --- | --- | --- |
| Named actual FULL native context and nested outer test | `NamedNestedFunctionalContext`, `NestedFunctionalOuterTestForward` | [#741](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/741) |
| Bidirectional true full functional reassociation | `FunctionalNestedReassociationReverse` | [#746](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/746) |
| COMPLETE contextual incompatibility-profile congruence for ALL rooted tests | `ActualContextualProfileCongruence` | [#750](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/750) |
| Entire old full functional outer root survives through exact retained complement | `GeometricOuterRootRetainedFullEmbedding` | [#752](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/752) |
| Actual old/new closed contexts have equal ALL-test profiles, with actual source coordinates | `GeometricOuterContextProfileCongruence` | [#753](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/753) |
| Literal OLD contextual vertex set equals old geometric outer piece | `OldOuterGeometricContextExactCarrier` | [#754](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/754) |
| Genuine ORIGINAL old piece and actual NEW context are profile-equivalent | `OriginalGeometricPieceToNewContextProfile` | [#767](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/767) |
| Full-root equality and global quotient-class equality preserve complete native function fibres | `FullRootStructureUniqueness`, `GlobalProfileFromFullRootCongruence` | [#776](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/776), [#781](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/781) |
| Pin the EXACT original Fin n order when reconstructing a true geometric minimal closed separator | `PrescribedGeometricOuterRoot` | [#788](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/788) |
| Equality of the actual original GLOBAL canonical piece relation symbol under explicit new geometric context/boundary conditions | `GeometricFlipGlobalSymbolCongruence`, `GeometricFlipGlobalSymbolFromBoundaries` | [#795](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/795), [#796](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/796) |
| ORIGINAL relation is realized in the real weak-image target, *provided old ordered-root target image is injective* | `GeometricFlipOuterTargetRelation` | [#819](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/819) |
| New source is finite for an ACTUAL selected geometric Q, and conditional global symbol follows without `Finite New` oracle | `SelectedGeometricFlipSourceFinite` | [#827](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/827) |
| The same genuine selected Q and fixed-root canonical gluing equivalence give original outer target relation, with exact old root tuple | `SelectedGeometricFlipOuterTargetRelation` | [#860](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/860) |
| Exact full source-context **carrier** from three component/attachment obligations, no assumed context equality | `FullFreeAmalgamExactTransportedContext` | [#868](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/868) |
| SOURCE-ATTACHED old geometric root closed preimage and exact `K_new = R_old ∪ C_new` | `GeometricTransportedContextExactCarrier` | [#871](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/871) |

All of the above are *conditional statements whose hypotheses are
part of their certified theorems*. In particular, neither completion
of a particular source flip nor global strong amalgamation follows
without the additional geometric and local support arguments below.

## Smallest visible input contracts for the nested-geometry assembly

Let `Old = Inner +_U E` and `New = Q +_U E` be actual FULL native
free-amalgam source diagrams. The older original closed root is
`T` (in `E`), possibly incomparable with `U`. Let `D` be the
old private inner component, `C_old` the old outer `T`-component,
and `C_new` a chosen new `T`-component.

The exact carrier bridge **#868/#871** now only asks for:

1. **Retained membership iff:** for each complement vertex
   outside `T`, membership in `C_old` is equivalent to membership
   in `C_new` under their two full embeddings. The generic theorem
   is already verified in Track A [#793](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/793)
   under genuine root-attachment hypotheses.
2. **Entire inserted private side:** every vertex of `Q` outside
   its full root `U` belongs to `C_new`. It is NOT enough that
   one chosen private component attaches: all private vertices
   must be accounted for. Draft [#884](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/884)
   attempts to derive connectedness of **ALL** private Q vertices
   from the actual selected geometric witness, using full rooted
   isomorphism. **Do not promote until complete CI succeeds.**
3. **Surviving common-root attachment:** each root vertex in
   `U \ T` attaches to `C_new`. The actual inserted-component
   theorem [#822](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/822)
   proves this from the chosen Q-private generated-root component.
   Anchors of the various component certificates must coincide;
   component basepoints cannot be silently identified.

These three assumptions imply the literal whole-source equation

`K_new = iNewInner(Q) ∪ iNewE(E ∩ oldOuterPiece)
       = iNewE(T) ∪ C_new.`

The new draft [#877](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/877)
uses that *derived* equality plus the still explicit new exterior
separation and BOTH complete generated-boundary equations to
obtain the old GLOBAL outer relation in the actual weak target.
It is **not yet CI-validated**.

## Other necessary geometric/root inputs (not supplied by the equation)

- **Outer-root survival:** the ordered old outer root does not meet
  the removed private inner component. Track A [#839](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/839)
  derives the genuine older exterior's disjointness from the
  complete inner root and removed component under true nested
  geometry, without pretending the two cuts are ordered.
- **Opposite generated boundary:** after the source flip,
  `Cl_New(N_New(C_new)) = iNewE(T)`, with FULL native partial-function
  closure, not just immediate Gaifman neighbours. The verified
  generated-boundary criterion [#763](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/763)
  derives it from retained membership plus the inner shared-root
  boundary contribution. The selected-Q specialization
  [#830](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/830)
  and conditional geometric restoration [#834](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/834)
  are also merged. Instantiating **all** their old/exterior
  geometric premises in one selected actual nested flip remains
  an integration obligation.
- **Opposite exterior component:** the retained exterior must
  remain a distinct genuine `T`-component with
  `Cl_New(N_New(C_ext)) = iNewE(T)`.
  Track A [#866](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/866),
  [#876](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/876),
  and [#879](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/879)
  investigate/assemble this; verify the exact final heads and their
  assumptions before counting them as complete.
- **Target root collisions:** weak EHN source-to-target maps need
  not be injective. The separate global relation witness can
  sometimes force injectivity of the relevant ordered tuple,
  but this is not a general injectivization theorem. Do not
  drop the explicit old outer tuple injectivity premise from #819.
- **Local termination:** a strict decrease of the B-only local
  SOURCE measure must preserve the selected outer piece's full
  root and global class; the terminal step must yield the original
  A-minimality contradiction. One-step B-support decrease alone
  does not prove this. Track C owns this, independently of Track B.
- **Unrestricted shadow avoidance:** even a correct Claim 2
  restoration is not by itself a verification of the original
  unrestricted Section 3 strong-amalgamation theorem. Its finite
  maximal trace age and original forbidden shadow-avoidance
  obligations require separate validation.

## Adversarial checks before any Claim 2 green marker

Do not identify a closed new context with a selected geometric
piece without the full-component equation and **both complete**
generated boundaries. Do not use a mere graph/relational reduct
to justify full native function reflection. Do not rely on
isomorphism closure of forbidden families that has not been assumed.
Do not infer a full embedding from a weak EHN map or collapse
distinct ordered root coordinates. Do not silently substitute the
selected Q component from one existential certificate for the basepoint
chosen in another without a verified component-equality lemma.

The frozen original paper prose is unchanged. Only validation
notes and separate mathematical documentation should be updated
until authorial decisions on the manuscript text.
