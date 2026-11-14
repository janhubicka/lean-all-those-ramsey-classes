import AllThoseRamseyClasses.Published.TrackEOriginalNativeInducedUIrreducible
import AllThoseRamseyClasses.Published.FunctionalWithParts2019GlobalProtectedControl
import AllThoseRamseyClasses.Published.TrackERetainTaggedNativeSystem2019
import PartiteConstruction.Functional.TrackEOriginalNativeClosedTestAdapter2019

/-!
# Track E: same-selected-map ORIGINAL native HE via ACTUAL exact tagged tests

The corrected 2019 global control protects every U-closed U-irreducible
tagged test. The canonical-tagged-test lift used by the earlier
conditional theorem is unnecessarily strong for an ACTUAL final
noncanonical sparse witness.

Here an original native full irreducible E-copy e determines its exact
range S in the final decoded native target. The existing full-irreducible
side-localization theorem proves that the ACTUAL induced tagged test C|S
is U-irreducible; the exact closure dictionary makes it U-closed. Apply
the SAME original tagged control f to precisely C|S. The existing
closed-exact-tagged-test decoder converts the resulting full tagged
embedding to a full partial-function embedding, while the new native
adapter removes unary labels and independent definedness bits.

The final composite is a genuinely FULL original set-valued function
embedding of E into the original control, on exactly f ∘ e. No extra
vertex, alternate control map, canonical retagging of the final witness,
weak image hull, or ambient domain reflection is introduced.

This is a same-map native HE INTERFACE for an existing final protected
tagged control. It does NOT construct the still outstanding finite-family
E2 sparse witness or class-local relative completions.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Q T : Type w}

/-- Any full irreducible original native E-copy in the ACTUAL final
decoded witness is protected by the corrected selected tagged control
on literally the same original map, without an extra canonical-tagged
lift of E. -/
theorem wholeMaskCovered_originalNativeCopy_selectedHE
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (Target : FunctionalPartite.System L Parts W) [Finite W]
    (f : V → W)
    (hTag : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts) C
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld
          Target.toStructure.toNonemptyPartial Target.part)) f)
    (E : Structure L T) (hE : E.Irreducible)
    (e : Structure.Embedding E
      ((wholeMaskOriginalDecode C).collapseDomain)) :
    ∃ g : Structure.Embedding E Target.toStructure,
      ∀ x : T, g x = f (e x) := by
  classical
  let A : PartialSetStructure L V := wholeMaskOriginalDecode C
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let S : Set V := Set.range e
  have hNativeClosed : A.collapseDomain.IsClosed S := e.range_isClosed
  have hOrigClosed : A.IsClosed S :=
    (A.isClosed_iff_collapseDomain_isClosed S).mpr hNativeClosed
  have hPlusClosed : Plus.IsClosed S := by
    intro F xs U hxs hVal
    exact hOrigClosed F.down xs U hxs hVal
  have hTestClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce S) :=
    wholeMaskCovered_decodedClosed_to_inducedUClosed
      C (Base.withParts basePart) basePart hC (hPos.withParts)
      hCover S hPlusClosed
  have hTestIrred :
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce S) :=
    wholeMaskCovered_originalNativeIrredCopy_UIrreducible
      C Base basePart hC hPos hCover E hE e
  obtain ⟨gTag, hgTag⟩ :=
    (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hTag).on_test
      (C.induce S) hTestClosed hTestIrred
      (RelStructure.inclusion C S)
  let TargetPlus : PartialSetStructure (L.withParts Parts) W :=
    Target.toStructure.toNonemptyPartial.withParts Target.part
  have hTransTarget :
      FibreTransversal Target.toStructure.toNonemptyPartial Target.part :=
    (nativeFunctionFibreTransversal_iff_partial
      Target.toStructure Target.part).mp Target.funcTransversal
  have hTransPlus : FibreTransversal TargetPlus Target.part :=
    (Target.toStructure.toNonemptyPartial.withParts_fibreTransversal_iff
      Target.part).mpr hTransTarget
  let gPart : PartialSetStructure.Embedding
      (Plus.wholeWeakInduce S) TargetPlus :=
    wholeMaskCovered_closedExactTaggedTest_toPartialEmbedding
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover S hPlusClosed
      TargetPlus Target.part hTransPlus gTag
  have hSourceEq :
      (Plus.wholeWeakInduce S).originalLanguageReduct.collapseDomain =
        A.collapseDomain.induce S hNativeClosed := by
    rw [originalLanguageReduct_wholeWeakInduce]
    have hDecoder : Plus.originalLanguageReduct = A :=
      originalLanguageReduct_actualWholeMaskDecoder C
    rw [hDecoder]
    exact wholeWeakInduce_collapse_eq_nativeInduce A S hOrigClosed
  have hTargetEq :
      TargetPlus.originalLanguageReduct.collapseDomain =
        Target.toStructure := by
    change
      (Target.toStructure.toNonemptyPartial.withParts
        Target.part).originalLanguageReduct.collapseDomain =
      Target.toStructure
    rw [originalLanguageReduct_withParts]
    exact Structure.toNonemptyPartial_collapseDomain Target.toStructure
  have hNativeMap :
      ∃ j : Structure.Embedding
          (A.collapseDomain.induce S hNativeClosed)
          Target.toStructure,
        ∀ x : S, j x = gTag x := by
    let gRaw : Structure.Embedding
        (Plus.wholeWeakInduce S).originalLanguageReduct.collapseDomain
        TargetPlus.originalLanguageReduct.collapseDomain :=
      gPart.originalNativeCollapse
    let j : Structure.Embedding
        (A.collapseDomain.induce S hNativeClosed)
        Target.toStructure := {
      toFun := gRaw.toFun
      injective := gRaw.injective
      map_rel_iff := by
        intro R xs
        simpa only [hSourceEq, hTargetEq] using
          (gRaw.map_rel_iff R xs)
      map_func := by
        intro F xs
        simpa only [hSourceEq, hTargetEq] using
          (gRaw.map_func F xs)
    }
    refine ⟨j, ?_⟩
    intro x
    rfl
  obtain ⟨j, hj⟩ := hNativeMap
  let inc : Structure.Embedding
      (A.collapseDomain.induce S hNativeClosed) A.collapseDomain :=
    Structure.inclusion A.collapseDomain S hNativeClosed
  have hRange (x : T) : ∃ y : S, e x = inc y :=
    ⟨⟨e x, ⟨x, rfl⟩⟩, rfl⟩
  let jE : Structure.Embedding E
      (A.collapseDomain.induce S hNativeClosed) :=
    e.factorThroughClosedRange inc hRange
  refine ⟨j.comp jE, ?_⟩
  intro x
  change j (jE x) = f (e x)
  have hjE : (jE x).1 = e x :=
    Structure.Embedding.factorThroughClosedRange_spec e inc hRange x
  calc
    j (jE x) = gTag (jE x) := hj (jE x)
    _ = f ((jE x).1) := hgTag (jE x)
    _ = f (e x) := congrArg f hjE

/-- The selected ORIGINAL native homomorphism upgrades to the full
2019 homomorphism-embedding: the genuinely partial global control
retains source-definedness, and every irreducible E-copy is full
by the preceding exact actual-tagged-test argument. -/
theorem wholeMaskCovered_originalNativeHE_of_selectedTaggedControl
    (D : FunctionalPartite.System L Parts V)
    (Target : FunctionalPartite.System L Parts W) [Finite W]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hD : D.toStructure = (wholeMaskOriginalDecode C).collapseDomain)
    (f : V → W)
    (hOriginal : Structure.IsOriginalPartialHomomorphism
      D.toStructure Target.toStructure f)
    (hTag : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts) C
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld
          Target.toStructure.toNonemptyPartial Target.part)) f) :
    Structure.IsOriginalPartialHomomorphismEmbedding
      D.toStructure Target.toStructure f := by
  refine ⟨hOriginal, ?_⟩
  intro U E hE e
  let eDec : Structure.Embedding E
      ((wholeMaskOriginalDecode C).collapseDomain) := {
    toFun := e.toFun
    injective := e.injective
    map_rel_iff := by
      intro R xs
      simpa only [hD] using (e.map_rel_iff R xs)
    map_func := by
      intro F xs
      simpa only [hD] using (e.map_func F xs)
  }
  obtain ⟨g, hg⟩ :=
    wholeMaskCovered_originalNativeCopy_selectedHE
      C Base basePart hC hPos hCover Target f hTag E hE eDec
  refine ⟨g, ?_⟩
  intro x
  exact hg x


/-- Upgrade the ACTUAL native 2019 sparse Ramsey witness, not merely
one supplied test or arbitrary conditional picture: the very same
selected control map furnished by the original two-pass construction
is an original native homomorphism-embedding on every irreducible full
native copy. Retain ALL existing partite Ramsey, canonical B-cover,
finite weak H-relative completion, and transversality certificates.

No canonical replacement of the final noncanonical tagged C is used.
The independent finite-family E2 construction and class membership
gates are not proved by this witness-level strengthening. -/
theorem genuinePartite2019_actual_standardSystem_sparse_witness_with_nativeHE
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hPos : L.PositiveFuncArity)
    (hIrr : ∀ {U : Type w} [Finite U]
      (P : PartialSetStructure L U) (p : U → Parts),
      H P p → FibreTransversal P p →
      (wholeMaskTagExpansion (withPartsWholeMaskOld P p)).Irreducible)
    {X Y Z : Type w} [Finite X] [Finite Y] [Finite Z]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (C0 : FunctionalPartite.System L Parts Z)
    (hB : H B.toStructure.toNonemptyPartial B.part)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hInitial : FunctionalPartite.Arrow A B C0 κ) :
    ∃ (VQ : Type w) (_ : Finite VQ)
      (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) VQ)
      (hClosed : IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
      (hCover : ∀ {U : Type w}
        (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) U),
        IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
        RelStructure.Embedding Test C →
        Nonempty (RelStructure.Embedding Test
          (genuineWithPartsTagged2019
            B.toStructure.toNonemptyPartial B.part))),
      ∃ (D : FunctionalPartite.System L Parts VQ),
        D.toStructure = (wholeMaskOriginalDecode C).collapseDomain ∧
        D.part = wholeMaskCoveredPart C
          B.toStructure.toNonemptyPartial B.part hClosed hCover ∧
        (∃ f : VQ → Z,
          Structure.IsOriginalPartialHomomorphismEmbedding
            D.toStructure C0.toStructure f ∧
          ∀ x : VQ, C0.part (f x) = D.part x) ∧
        (∀ S : Finset VQ, S.card ≤ n →
          HasGenuinePartiteTagged2019RelativeCompletion H
            (C.induce (↑S : Set VQ))) ∧
        FibreTransversal (wholeMaskOriginalDecode C)
          (wholeMaskCoveredPart C
            B.toStructure.toNonemptyPartial B.part hClosed hCover) ∧
        FunctionalPartite.Arrow A B D κ := by
  classical
  obtain ⟨VQ, hVQ, C, hClosed, hCover, D, hD, hPart,
      ⟨f, hTag, hOriginal, hMapPart⟩, hWeak, hTrans, hArrow⟩ :=
    genuinePartite2019_actual_standardSystem_sparse_witness_with_taggedHE
      H hHer hStrong hIso hPos hIrr A B C0 hB n κ hInitial
  have hNativeHE :
      Structure.IsOriginalPartialHomomorphismEmbedding
        D.toStructure C0.toStructure f :=
    wholeMaskCovered_originalNativeHE_of_selectedTaggedControl
      D C0 C B.toStructure.toNonemptyPartial B.part
      hClosed hPos hCover hD f hOriginal hTag
  exact ⟨VQ, hVQ, C, hClosed, hCover, D, hD, hPart,
    ⟨f, hNativeHE, hMapPart⟩, hWeak, hTrans, hArrow⟩

end AllThoseRamseyClasses.Published
