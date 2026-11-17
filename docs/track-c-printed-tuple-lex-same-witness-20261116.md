# Track C — printed tuple-image closure with one simultaneous lexicographic witness

16 November 2026. New native Lean endpoint and protected axiom checks.
Source add-only; frozen 2019 numbered manuscript unchanged.

## Mathematical improvement over merged #1259

Merged #1259 used a strengthened forbidden-family hypothesis: closure
under ALL actual vertex-surjective EHN images. The original Section 3
printed condition only asserts that a tuple-surjective original partial
homomorphism-embedding image CONTAINS some full forbidden member.

New `forbiddenEHNWitness_injectiveReplacement_allSupport_of_printedTupleRange`
takes exactly that weaker printed closure plus ONE chosen original
finite forbidden EHN weak map with a FUNCTION-CLOSED actual target
range and a genuine ORIGINAL partial tuple-surjective map to the
induced full native target range. A SINGLE forbidden full subimage
P is selected by the printed image-closure condition. Select a
preimage for every P vertex under the actual surjective source-to-range
factor. This is an INJECTIVE selector, independent of the target
Active subset; consequently the SAME injective forbidden P witness
has no larger SOURCE support on EVERY target Active at once.

This repairs the lexicographic selection: A-source nonincrease alone
would not preserve B-minimality among A-minima, but simultaneous A
and B source inequalities do. A and B both count SOURCE vertices,
never weak target image vertices or quotients.

## Exact endpoints

- `claim2_injectiveLexMinimum_smallestMixed_hasStrictBAflip`:
  an IMAGE-CLOSURE-FREE extraction of the already verified all-width
  geometric theorem. For ONE injective globally (A,B)-lex-minimal
  original F-forbidden EHN source with its smallest genuine mixed
  minimal separator, the actual new forbidden source has STRICTLY
  lower total B-only SOURCE count and STRICTLY higher total A-only
  SOURCE count. This is a cost obstruction, NOT a contradiction.
- `exists_selectedPrintedTupleLex_injective_minimalMixed`:
  under printed closure and ONE selected lex-minimal original
  source with closed, tuple-surjective induced target range,
  obtain the SAME injective original lex-minimal forbidden source
  and its genuine smallest mixed positive-width geometric piece.
- `exists_selectedPrintedTupleLex_actualFlip_strictBA`:
  combine the preceding two on the SAME source to get an actual
  B-down/A-up forbidden original source replacement.
- `exists_printedSelectedLexInputRelation_actualFlip_strictBA`:
  sufficient SOURCE-LOCAL tests for the CHOSEN lex minimizer:
  every original function input is protected by a full irreducible
  source test, and every positive OLD target relation tuple on
  the actual image range has an original positive source tuple
  preimage. The first produces closed range and exact full
  function fibres; together they produce the required tuple
  surjectivity and the actual replacement.
- `exists_printedLexInputRelation_covers_actualFlip_strictBA`:
  start from ANY nonempty forbidden original EHN witness, select
  a genuine global lex minimum using the verified existing theorem,
  and apply the preceding result if all such lex-minimal sources
  have these TWO LOCAL source certificates. No assumptions on
  arbitrary nonminimum sources.
- `forbiddenEHNWitness_injectiveReplacement_allSupport_of_printedTupleRange`
  described above is the sixth endpoint.

## What has NOT been proved

1. The printed forbidden-family axioms, connectedness, and regularity
   alone do NOT imply that lex-minimal witnesses have all
   irreducible function-input tests or relation-tuple preimages.
   The relation coverage is especially delicate: the old
   C5/ternary-relation counterexample exposes failures of
   automatic relation reflection.
2. The selected Q from the genuine all-width B-to-A flip generally
   has new A-exclusive source vertices. Its global A-minimality
   is NOT preserved, and one must not iterate the original
   A-minimizer proof with that hidden assumption.
3. The total B source decrease and A source increase are not a
   contradiction to lexicographic minimum. Original unrestricted
   Claim 2 and strong AP remain UNPROVED.
4. No auxiliary weak-image quotient is substituted for the full
   original induced target structure. No deleted collaborator
   TODOs are reinstated. No modifications to manuscript.

Active proof roots and explicit `#print axioms` are supplied for
each module. This is DRAFT until exact-head all-module Lean, allowed
axioms, import, no-admission, and source/inventory CI passes.
