# Track D — verified reductions and remaining Section 3 root-collision gate (12 November 2026)

This is the CURRENT checkpoint; the older
[`lifts-track-d-root-collision-20261101.md`](lifts-track-d-root-collision-20261101.md)
is preserved as a historical audit. All results below refer to the
actual native functional language and original 2019 `ramsey.tex` Section 3.
**The printed manuscript is frozen**; this note adds no validation marker
or collaborator TODO back to that document.

## The image-closure contract and the counterexample

The printed image closure applies to tuple-surjective
original-partial homomorphism-embeddings and concludes that the
target **contains** an induced forbidden member. It does NOT claim
that every vertex-surjective weak EHN image is itself a forbidden
member, that the full range reflects all relation tuples, or that
the weak quotient fully embeds into an arbitrary target.

The exact source-generated quotient is tuple-surjective, but its
inclusion in the target is only weak in general. This is not a technical
gap which can be solved by simply asserting full range closure.

**Verified on main:** `fiveCycleImageFamily_counterexample_to_blanketInjectivization`
in `Lifts/EHNFiveCycleNoInjectiveReplacement.lean`, with supporting
`EHNFiveCycleImageClosedFamily` and `EHNFiveCycleImageFamilyConnected`,
gives a finite connected family satisfying the *printed* image
closure and a noninjective forbidden EHN witness with NO injective
replacement in the same target. This refutes the unrestricted
injectivization shortcut, **not** strong AP for compatible canonical
maximal lifts.

## Current positive formalized reductions

* **Actual root/image geometry:** `minimalGlobalForbiddenWitness_collidingRoot_or_mixedPiece`
  yields a genuine positive-width geometric forbidden piece in the
  actual full free amalgam. Its collision alternative is not suppressed.
  `ehn_injOn_of_rootPairsCoveredByIrreducibleTests` conditionally
  rules out root collisions when full irreducible source tests cover
  each root pair; the cover itself is NOT automatic.
* **Actual quotient reflection defects:** merged PRs
  [#898](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/898),
  [#907](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/907),
  [#908](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/908),
  [#915](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/915)
  establish that a bad FULL irreducible weak-image test factoring into
  a genuine free-amalgam side exposes extra target relation/function
  incidence; the covered-function-input case eliminates the
  function surplus only under its EXPLICIT source test cover.
* **Local uncovered function inputs:** merged
  [#912](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/912)
  establishes that a side function surplus forces unprotected original
  source input tuples whose original function fibre is EMPTY. It
  also supplies genuinely native source hull decompositions, and
  a language-restricted injectivization theorem for nullary/unary
  functions without relations or total source functions without relations.
* **Actual crossing representatives:** merged
  [#989](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/989)
  exhibits actual source preimage representatives of relation/function
  surplus coordinates with a proper FULL free decomposition crossed
  by their input generators; a collision on any pair of distinct
  generators similarly forces a genuine crossing root-hull decomposition.
  This does NOT identify the decomposed hull with a genuinely
  selected forbidden geometric piece.
* **Unary input-test coverage:** merged and exact-head Lean-verified
  [#1001](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1001)
  proves the unary relation-input analogue and injective support-minimal
  forbidden EHN witnesses for nullary/unary native languages, or
  arbitrary-arity functions total on forbidden sources with unary
  relations. This is a language-restricted positive result under
  the printed image-closure contract, not unrestricted Section 3 AP.
* **Exact conditional normalization-to-geometry handoff:** merged
  [#1004](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1004)
  produces a globally source-support-minimal **injective** EHN
  forbidden witness and its smallest genuine mixed geometric piece,
  assuming the *printed* image closure PLUS explicit full irreducible
  source-test coverage for EVERY native function and relation input.
  Those coverage assumptions are NOT consequences of forbidden-source
  connectedness/regularity.

Every item described as *merged* is backed by a successful exact-head
Lean build, named permitted-axiom checks, source-contract/integrity
audits and no-admissions scan. The results are conditional exactly
as stated; the module or PR must be consulted before using them.

## Verified post-incidence improvements on main

These results have been **merged** following successful exact-head Lean
build, named axiom, source-integrity, Section 3 contract and admission
checks. None proves unrestricted original Section 3 strong AP.

* [#1017](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1017):
  a colliding genuine separator-root tuple forces an ACTUAL proper
  FULL native free decomposition of the root-generated source hull,
  with neither side containing every root generator. The hull is
  not asserted to be a selected forbidden geometric piece.
* [#1028](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1028):
  ONE already source-support-minimal witness can be normalized
  injectively if its own native function inputs have full irreducible
  source tests and target OLD relations on its actual range have
  positive source lifts. No all-forbidden-sources cover assumption.
* [#1034](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1034):
  a minimal witness has an uncovered crossed function input, a target
  relation defect with crossed source inputs, OR an injective
  support-minimal witness with a smallest genuine mixed piece.
* [#1046](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1046):
  sharpens the first branch to an ACTUAL target-only positive function
  incidence with NO original positive lift at ANY matching source
  input/output coordinates; keeps native function-value fibres and
  original source support distinct from target-image counts.
* [#1054](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1054):
  every globally unliftable positive native function/OLD relation
  target incidence in a genuine FULL free amalgam belongs to ONE
  actual FULL side, while its original generated source input hull
  has a proper FULL decomposition crossed by the generators.
* [#1059](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1059):
  upgrades the original minimal-witness trichotomy so BOTH kinds of
  side-local positive incidence have NO positive original source
  lift at ANY matching preimage tuple; the function case proves
  that every matching original source input fibre is EMPTY.
* [#1067](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1067):
  absence of BOTH genuine side-local incidence defects is EQUIVALENT
  to original-partial tuple coverage on the ACTUAL function-closed
  induced image. On genuine EHN maps, defined-function DOMAIN
  coverage is equivalent to COMPLETE value-fibre coverage:
  one positive original application generates an irreducible full
  source input hull, on which EHN is full. Its conditional
  one-minimizer handoff yields an injective minimal forbidden witness
  and smallest mixed piece when both defects are absent.

The exact original-partial encoding currently uses NONEMPTY native
set-valued fibres for defined function domains. An independent
defined-but-empty domain-token convention would need a separate
representation. The source-generated weak quotient is not silently
identified with the true full induced target image.

## Current proof development — pending exact-head CI

* [#1084](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1084):
  draft source-hull EHN factorization. If all source input
  generators map into one FULL target side, their ENTIRE native
  function-closed generated source hull does, and the induced
  hull factors EHN into that side with original coordinates.
  When that side is `Forb_EHN(F)`, its preimage hull is itself
  `Forb_EHN(F)`, even if reducible and properly free-decomposable.
* [#1088](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/1088):
  stacked draft separation of an incidence into **common-seam-only
  source input hull** versus **actual left/right-exclusive original
  source input generator**. In the former case the entire hull EHN
  factors into the FULL common root. For a positive native function
  incidence, all-root inputs force its target output into that root
  because the common root is function-closed. The latter case has a
  genuine exclusive source input potentially useful as a flip anchor.

These are drafts and are not counted as kernel-certified until
their exact-head build, named permissible axioms, source-integrity
and no-admissions checks complete and they are merged.

## Adversarial strategy for the remaining maximal-lift step

There are now two genuinely different configurations, not an
unexplained global injectivization assertion:

1. **Seam-only defect.** All original source incident inputs map into
   the shared root; the native input-generated source hull EHN-factors
   into that root. For functions the positive output is also in the
   root. A complete ORIGINAL common global lift only identifies
   canonical added relations on corresponding root tuples, and
   the ORIGINAL added relation is false on NONINJECTIVE tuples.
   A proof based on an added predicate at a collided root cannot
   silently use positive root-relation realization.
2. **Exclusive-input defect.** At least one ACTUAL source generator
   maps into an exclusive side. This gives a plausible source-side
   anchor for a support-decreasing flip, but the crossed input
   hull is NOT automatically a genuinely selected minimal-closed-
   separator forbidden subpiece; its precise root, private source
   component, old-language structures, canonical global symbol and
   source support change remain to be constructed.

If the target side is `Forb_EHN(F)`, an EHN factorization of
the whole source-generated hull shows that the hull is also
`Forb_EHN(F)`; hence **side forbidden-freeness does not rule out
the defect**. It is not legitimate to assume the hull contains
a forbidden full/EHN witness or to use the quotient as a full
embedding. A successful repair must build a genuine forbidden
extension/selected source piece compatible with maximal global
rooted profiles, or give a collision-tolerant source flip.

### Two-vertex sanity check: forbidden-free crossed hulls really occur

This is a **mathematical illustration, not a new Lean certificate or
a counterexample to common-maximal-lift strong AP**. Work in the
plain loopless graph language and forbid the triangle. Let `H`
consist of two isolated vertices and let `S` consist of one edge
on two vertices. The identity-on-vertices map `H → S` is a weak
EHN homomorphism-embedding: the only nonempty irreducible full
tests of `H` are singletons, and these embed fully into `S`.
Both `H` and `S` are triangle-free. Nevertheless the target
edge is a positive incidence with NO positive source edge lift;
the two generators of `H` cross its genuine two-singleton full
free decomposition.

Thus the local configuration “unliftable target relation inside a
forbidden-free full side + crossed, forbidden-free source-generated
hull + an EHN factor into that side” is **consistent** with
ordinary forbidden-freeness. To derive a contradiction in the
ACTUAL Section 3 setting one must use the full forbidden source
`w`, the real seam/geometry of its selected pieces and the complete
common maximal canonical lift; these hypotheses do NOT occur in
the two-vertex toy example.

The original printed canonical added relations require injective
root tuples; the separate folded-root construction does not
automatically supply an ORIGINAL full common lift. Do not exchange
those two lift predicates in an unrestricted theorem.

## Critical remaining proof obligation

An **unrestricted** proof of original regular-family strong AP
requires either:

1. a genuine maximal-common-lift argument excluding these
   reducible, uncovered separator-root / source-input configurations
   under the exact original 2019 hypotheses; OR
2. a collision-tolerant forbidden-source flip preserving the
   ACTUAL old-language finite source, the full canonical root
   profile, and strict decrease of the ORIGINAL source A-exclusive
   support count, without false target-root injectivity.

Crossing free decompositions of a *root-generated closed hull*
alone are **not** flippable geometric forbidden subpieces. The
literal root cut, selected private component, ordered symbols,
target-root map and source-side support accounting must all be
re-established before invoking any Track C descent.

Even a solved Track D collision case would leave Track C's
arbitrary-positive-rank genuine selected-Q successor and terminal
A-minimizer contradiction as independent obligations.

**No unrestricted Claim 1 / Claim 2 / Section 3 strong AP or Ramsey
statement is currently kernel-certified.**
