# Track D: exact corrected full-image normal form

## Scope

The repaired family is G = FullRangeEHNSaturation F, not the original F. An element of G is a full target structure of a vertex-surjective EHN map from a finite original forbidden member. Additional positive target tuples are allowed. No weak source-generated quotient is called a full substructure.

The new native Lean module FullRangeSaturationNormalForm proves, subject to exact-head CI:

1. When the actual image range is function-closed, the FULL induced target image of an original finite forbidden EHN source belongs to G. This conditional statement includes native functions.
2. Saturation is idempotent and is the least class containing the finite original members and closed under vertex-surjective EHN images. These statements also include native functions.
3. In a relational language, Forb_EHN(F) is EXACTLY the class with no FULL embedded member of G. Neither the ambient target nor the original family needs a cardinal bound for this equivalence.
4. Starting with an original forbidden witness, one can choose a globally source-support-minimal G-witness whose map into the same target is an actual FULL embedding. This strengthens the parent module's merely injective EHN endpoint.

## Proof of the full-embedding endpoint

First take the verified-API candidate for an injective support-minimal G-witness w. Replace its source by the target's full induced structure on range(w). The factorization is surjective EHN, so G's image closure applies. Inclusion of this structure is a full embedding by construction. Since w is injective, its support over the designated target subset is in literal bijection with the new support; the original minimum is preserved exactly, not inferred from image cardinality. The result is packaged as a genuine ForbiddenEHNWitness over G.

## Verification boundary

These are newly written native Lean proofs, not yet certification claims. Five named axiom checks and an active-root entry are included. The existing PR must pass its exact-head all-module build, named axiom checks, source/import contracts and inventory before merge. A full compiler log artifact is now preserved so compilation errors can be examined without replayed warning floods.

## Not yet concluded

This does not identify the original and repaired canonical lifts. The original counterexample is not repaired by retaining the same family. Finiteness up to isomorphism for finite families in finite relational signatures follows mathematically from the bounded original source size, but its native enumeration bridge is not supplied here. Regularity of saturation for arbitrary infinite regular families, function-closedness of arbitrary native images, and the full Track C geometric iteration remain separate obligations. The frozen numbered manuscript is unchanged.
