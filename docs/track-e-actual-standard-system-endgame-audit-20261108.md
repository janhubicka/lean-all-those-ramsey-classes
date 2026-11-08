# Track E — actual native FunctionalPartite endgame (2026-11-08)

**Status: proof source proposed; CI has not certified it.** This note is
an independent English statement/proof audit for
`TrackEActualStandardSystemSparseWitness.lean`. It does not change the
frozen 2019 source manuscript.

## Precise statement and quantifiers

Let `A,B,C₀ : FunctionalPartite.System L Parts` be finite native
set-valued-function partite systems. Let `H` be the **genuinely partial**
`Option(Set)` class with precisely the inherited hypotheses:
closed hereditary, partite strong AP, isomorphism closure, positive
primitive function arities, and the irreducibility hypothesis for
canonical full tagged H members. Assume `B.toStructure.toNonemptyPartial`
belongs to H and assume the **standard** full partite arrow
`FunctionalPartite.Arrow A B C₀ κ`.

The asserted conclusion has one finite tagged final witness `C`,
one recovered `D : FunctionalPartite.System L Parts VQ` on the
**identical carrier VQ**, and the following:

1. `C` is U-closed with canonical closed-U-irreducible B-copy coverage.
2. `D.toStructure` is definitionally the **native collapse of the
   actual original decoder** of `C`, while `D.part` is definitionally
   its existing protected B-covered part map.
3. There exists the **same** original-source-defined control map
   `f : VQ → Z`; it preserves all parts and gives
   `Structure.IsOriginalPartialHomomorphism D.toStructure C₀.toStructure f`.
   This is NOT a total-fibre / domain-reflecting homomorphism.
4. For **every exact** finite vertex subset `S ⊆ VQ` with
   `|S| ≤ n`, the exact ambient tagged weak induced
   structure `C.induce S` has a genuine H-relative completion.
   No test is enlarged to its closure hull, nor replaced by
   an intrinsic weak restriction of the decoded target.
5. `FunctionalPartite.Arrow A B D κ`, on the same full A/B copy
   spaces and same colour set κ.

**Not claimed:** `H D`, strict mixed-root functional B-trees,
full fibre/domain reflection for `f`, unconditional ordinary
2019 K→H completion, or the historical unrestricted 2019
statement.

## Independent proof audit

1. `#947`: exact composition-preserving bijection identifies the
   initial standard arrow with `NativePartPreservingArrow`.
   This retains part labels of isolated vertices.
2. `#940`: for each native input System, the full-function
   transversality field is equivalent to `FibreTransversal`
   of its nonempty-fibre partial encoding. Undefined native inputs
   remain undefined, not `some ∅`.
3. `#924` + `#940`: obtain the ACTUAL 2019 tagged final `C`,
   `hClosed`, `hCover`, control map, exact local H
   certificates, partial transversality and true native part-preserving
   arrow. No fresh or repaired `C` is chosen.
4. `#944`: every primitive old relation tuple in final `C`
   has a literal ordinary irreducible exact-support test.
   Protected B-coverage gives a FULL canonical B embedding of
   that exact test, which preserves and reflects both the old tuple
   and each unary part predicate. Since the original B is
   a `FunctionalPartite.System`, equal part labels imply
   equal corresponding relation vertices; injectivity pulls this
   equality back to `C`. The empty tuple case carries no
   coordinate pair to check.
5. `#953`: the native decoder and recovered part map now carry
   both **independent** transversal properties. Form
   `sameCarrierFunctionalPartiteSystem`; its underlying
   Structure and its part map are definitionally the old values.
6. `#947/#953`: the native full part-preserving arrow transfers
   to the standard `FunctionalPartite.Arrow` without changing
   full embeddings or their composition.
7. Every remaining conclusion is inherited from step 3;
   the displayed `D` is not required to be an H member.

## Adversarial missing-assumption checks

- **Do not drop relation transversality of B.** Two distinct
  same-part vertices in a binary relation, with no functions,
  satisfy function-fibre transversality vacuously but violate
  `FunctionalPartite.System.relTransversal`.
- **Do not infer H-membership of D** from all small exact weak-test
  certificates. That requires the *separate* corrected class-local
  completion axiom, uniformly for the relevant cutoff.
- **Do not strengthen global control to total homomorphism.**
  An undefined function input can map to a defined one.
- **Do not replace weak S with an intrinsic weak restriction.**
  Clipped function fibres can create new irreducibles.
- **Do not assume ordinary ordered classes automatically fit
  `FunctionalPartite.System`.** If the language has a binary
  order relation between distinct same-part vertices, the System
  transversality field fails. This result therefore covers the
  specified genuine partite Systems, not all arbitrary ordered
  expansions of H.

## Repository status and next gates

The integration branch stages the unchanged #940 and #944 modules
alongside #947/#953 for a single exact-head build, with one new
theorem and a named axiom-check root. Those independent files can
be deduplicated during normal PR integration. A Lean kernel proof
has **not** been certified by this note.

Required before merge:
- [ ] Exact-head full Lean project build and dependency-resolved imports.
- [ ] Named `#print axioms` inventory: only standard Lean axioms.
- [ ] Active-root/no-sorry/no-admit and source-contract inventory.
- [ ] Adversarial declaration audit for extra assumptions and correct
      hCover definitional equality across `genuineWithPartsTagged2019`
      and `wholeMaskTagExpansion (withPartsWholeMaskOld ...)`.
- [ ] Separate corrected class-local completion theorem to obtain
      an actual H-member; do not mark as included in Track E.

