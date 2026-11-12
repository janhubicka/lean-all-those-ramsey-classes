# Track C — adversarial audit of the corrected functional rank increment

**Date:** 12 November 2026. **Status:** New Lean modules on draft PRs #1040 and #1042, exact-head CI pending. The frozen survey TeX has not been edited.

## Where the proof now genuinely stands

The merged and axiom-audited library proves:

- Exact function closure = relative U-closure for a corrected-(4b) tagged candidate; the minimal number of functional generators equals its U-size. This says nothing about the number of vertices in a generated hull (PRs #910, #923).
- Every ordinary irreducible weak induced test has a full canonical H-target under corrected (4b) and ambient irreducibility. Every test whose U-hull is U-irreducible has a canonical H-relative completion as well (PRs #934, #936, #963).
- Completions of all U-closed induced tests of generator rank <= j imply completions of every exact ambient weak test of cardinality <= j; the map and exact tested weak source are preserved (PR #935).
- Genuine H-relative completions glue across a **single common closed K(H) boundary** if their weak source is a free amalgam of relatively U-closed side ranges and H has strong part-preserving amalgamation. This is conditional on the boundary; it does not construct it (PR #938).

## New fixed-B-free weak rank cut (draft PR #1040)

Fix j, an ambient U-closed C satisfying corrected (4b) for K(H), and suppose every U-closed induced test in C of U-size <= j is H-relatively completable. For exact weak S on <=j+1 vertices:

1. The verified weak-rank dichotomy either supplies a K-completion of S from the closed rank-j invariant, or shows |S|=j+1 and every subset of S is relatively U-closed.
2. If S is ordinary irreducible, corrected (4b) plus the canonical weak irreducible completion theorem completes S. The H-target depends on S; **no fixed B-cover** is assumed.
3. Otherwise the verified free-decomposition lemma gives S = Left ⊕_Root Right. Both side carriers are proper and hence of cardinality <=j; because all subsets of S are relatively U-closed, both side embeddings have relatively U-closed ranges.
4. **Missing:** it does not follow that Root is U-closed, U-irreducible or belongs to K(H). A weak root may retain active OLD closure-domain data with its actual output omitted.

This is a genuine alternative to the earlier fixed-B-coverage proof of the weak free-cut lemma.

## Rank-j side completions require no extra oracle (draft PR #1042)

The original #1042 sketch separately assumed completability of all smaller embedded weak sources. That premise is redundant.

For a full embedding e : D -> C where |D|<=j, let T=e[D] be the exact finite range. Then |T|<=|D|<=j. The verified closed-U-rank bridge yields an H-relative completion of the EXACT OLD induced test C|T. Precompose its induced-closed U-homomorphism-embedding with the full embedding D -> C|T. This produces an H-relative completion of D with the *same target* and no closure hull in the conclusion. It keeps independent OLD domain-mask bits.

Therefore each side of the proper cut in #1040 is automatically H-completable from **the one closed rank-j premise**.

## Conditional rank step and its contrapositive

Under the standing (4b), ambient irreducibility, H-strong amalgamation and closed rank-j completion premises, add only:

> (**Boundary condition**) The common Root of every proper free weak cut selected in the rank dichotomy belongs to K(H).

Then the already verified genuine H gluing lemma gives a completion of every exact weak S of size <=j+1. No independent side-completability assumption remains.

Conversely, if some exact weak S of size <=j+1 is not completable, that rank dichotomy gives a proper free cut of S with relatively U-closed proper side ranges, both sides completable, **and Root not in K(H)**. Otherwise gluing would contradict non-completability. This is a necessary obstruction, not an existentially proven repair.

## Still open: the actual Hales–Jewett/Picture boundary mechanism

The fixed-B-free reduction and the conditional rank step do **not** prove the complete original functional local-finiteness theorem. The missing boundary condition may be false for an arbitrary free cut; one cannot simply "complete" the weak common root independently, because it may require closure outputs not present on either side and the chosen completions might interpret them incompatibly.

The actual Picture history may need a *protected closed boundary in the projected ambient control* rather than the raw weak intersection, and compatible maps of both side completions into/over that same boundary. The previously checked projected-rank gluing modules provide conditional tools; verifying that the actual stages supply the needed projected generator budgets is a separate requirement.

Do not identify the printed survey local-finiteness condition (all actual CLOSED substructures with <=n VERTICES have completions) with the stronger rank-n closed-test premise (all closed substructures with U-size<=n may have many more vertices). The latter was an explicit temporary induction invariant, not an implication established from the printed class hypothesis.

No claim is made about nullary primitive functions beyond the theorem contracts actually used, no strict native B-tree theorem is inferred, and no full embedding of an arbitrary intrinsic nonclosed weak functional restriction is assumed. All current source and test carriers remain exact.


## Sharper obstruction under original H-isomorphism closure (new draft lemma)

The exact original functional theorem also assumes H is closed under part-preserving full functional isomorphisms. The merged canonical-image theorem transfers this to the relational class K(H). Under that assumption the noncanonical-root conclusion above refines to:

> A noncompletable j+1-small weak test admits a proper relative U-closed-sided free cut whose common Root is **either not intrinsically U-closed or not U-irreducible**.

Proof: embed the common Root into the original corrected-(4b)-covered candidate C by composing the root-to-side map, the side-to-weak-test map, and the exact induced weak-test inclusion. If Root were both U-closed and U-irreducible, the verified induced-versus-abstract corrected (4b) coverage equivalence, using isomorphism closure of K(H), would force Root ∈ K(H). But the conditional rank-step obstruction shows Root ∉ K(H). Thus at least one of the closedness/irreducibility properties fails.

This is a necessary obstruction and not a complete dichotomy with available repairs: a nonclosed common root may require extra closure outputs; a closed but U-reducible root may require another gluing decomposition. The proof is a new axiom-registered declaration in PR #1042, **not green until CI**.
