# Appendix Track B — actual native partite strong amalgamation

6 November 2026. Stacked on the class-identity/heredity PR #890. All existing source lemmas and the frozen survey manuscript remain untouched.

## Mathematical input and native construction

Given three ACTUAL finite native partite functional systems Root, Left, Right belonging to the SAME native class K, and two FULL native PART-PRESERVING root embeddings sL and sR, define S=range(sL) inside Left. The existing `Structure.Embedding.range_isClosed` gives genuine native function-closedness of S. The existing `Structure.Embedding.factorThroughClosedRange` constructs a FULL embedding g:Left|S → Root by inverting the range copy. Its part-preservation follows directly from sL.map_part and the identity of source vertices.

The map f = sR ∘ g : Left|S → Right is a full part-preserving embedding. Apply the existing functional partite `Attachment.attach` to one full LEFT copy with core Right along f. The verified source `Attachment.unit_isFreeAmalgam` gives EXACT overlap, no additional identifications. The native `Structure.FreeAmalgamationClass K` supplies K membership of the resulting target, and `FunctionalPartite.Attachment.attach` supplies output transversality for genuinely SET-VALUED operations. Both sides embed fully and preserve complete function fibres and vertex parts.

## Lean declarations

- `NativeKPartiteStrongAmalgamation2019`: the exact finite native strong part-preserving amalgamation proposition, including full embeddings of both sides and exact agreement/overlap over Root.
- `nativeKPartiteStrongAmalgamation_of_free`: constructs a literal target from the existing native one-copy free-attachment API under `Structure.FreeAmalgamationClass K`.

This proof is wholly in the actual FUNCTION language, not in a fabricated OLD relation-power or semi-closed tree. It does not complete a nonclosed weak source nor infer any false full embedding of original-partial EHN projections.

## Next correspondence

A separate theorem will transport native partite strong amalgamation to the faithful genuinely partial H_K class of PR #882 by the FULL native/faithful partial embedding equivalence. This requires preserving the original part map and its exact target overlap, and must not assume all Option(Set) structures (particularly some-empty values) are in the native image.

Neither this native theorem nor its forthcoming transfer establishes the stronger 2019 ambient-relative local completion axiom; that remains Track C.

Validation: draft until exact-head full Lean build, source integrity audit, and named `#print axioms` succeed; no `sorry`, no new axiom, no survey text change.
