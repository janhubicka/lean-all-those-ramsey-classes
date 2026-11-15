import AllThoseRamseyClasses.Published.TrackEOriginalNativeInducedUIrreducible
import PartiteConstruction.Functional.TrackEInternalTaggedBCopyNativeDescent2019
import PartiteConstruction.Functional.TrackEFinalCoveredDecodedClosedU2019

/-!
# Track E: a protected internally-B-covered final tagged C covers native irreducibles

For the ACTUAL final whole-mask part-labelled tagged 2019 C, the verified
native irreducibility transfer says that every FULL native irreducible
E-copy e:E↪wholeMaskOriginalDecode(C).collapseDomain has a literal
U-irreducible exact induced tagged image C|range(e). The verified
exact closedness dictionary makes that SAME image intrinsically
U-closed, since a full native e has a function-closed range.

Under the corrected 2019 class assumptions, external canonical-B
coverage upgrades this exact tagged U-test to an ordinary irreducible
test: it is a closed-U hereditary K member, and all K members are
ordinarily irreducible. INTERNAL canonical tagged B-copy extension
therefore yields an actual full Btag-copy in the SAME C covering the
literal image e[E].

The separate full OLD→Option(Set) decoder and full partial→native
collapse convert this INTERNAL Btag-copy into a FULL native B-copy in
wholeMaskOriginalDecode(C).collapseDomain, whose range contains e[E].
All selected vertex maps and all full multi-valued fibres are retained.

This gives the exact native internal-B-extension contract needed in
Appendix A Track E. It does not assert that the hypotheses hold for
every arbitrary relational target. The actual construction of internal
Btag copies is the unverified coordinated postprocessing stack.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V B : Type v}

/-- On the ACTUAL final B-protected whole-mask tagged witness, every
full native irreducible copy e:E↪D lies inside a FULL native B-copy of
THE SAME decoded native D. No enlargement of e[E], replacement of D,
or alternate selected control map is used in this extension statement. -/
theorem wholeMaskCovered_nativeIrredCopy_internalB
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L B) [Finite B]
    (basePart : B → Parts)
    (hTrans : FibreTransversal Base basePart)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    {K : RelStructure.StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts)}
    (hBaseK : K (wholeMaskTagExpansion
      ((Base.withParts basePart).wholeMaskPatternGraph basePart)))
    (hHer : ClosedUHereditary K
      ((L.withParts Parts).wholeMaskClosureRules Parts))
    (hKIrr : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      K Test → Test.Irreducible)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hInternal : IrreduciblesExtendTo
      (wholeMaskTagExpansion
        ((Base.withParts basePart).wholeMaskPatternGraph basePart)) C)
    {T : Type v} (E : Structure L T)
    (hE : E.Irreducible)
    (e : Structure.Embedding E
      ((wholeMaskOriginalDecode C).collapseDomain)) :
    ∃ beta : Structure.Embedding Base.collapseDomain
        (wholeMaskOriginalDecode C).collapseDomain,
      ∀ x : T, ∃ b : B, e x = beta b := by
  classical
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  have hNativeClosed :
      ((wholeMaskOriginalDecode C).collapseDomain).IsClosed
        (Set.range e) := e.range_isClosed
  have hOriginalClosed : (wholeMaskOriginalDecode C).IsClosed
      (Set.range e) :=
    ((wholeMaskOriginalDecode C).isClosed_iff_collapseDomain_isClosed
      (Set.range e)).mpr hNativeClosed
  have hPlusClosed : Plus.IsClosed (Set.range e) := by
    intro F xs U hxs hVal
    exact hOriginalClosed F.down xs U hxs hVal
  have hTagClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (Set.range e)) :=
    wholeMaskCovered_decodedClosed_to_inducedUClosed
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover (Set.range e) hPlusClosed
  have hTagIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (Set.range e)) :=
    wholeMaskCovered_originalNativeIrredCopy_UIrreducible
      C Base basePart hC hPos hCover E hE e
  obtain ⟨beta, hBeta⟩ :=
    wholeMaskCovered_internalTaggedB_to_native_of_closedUIrred
      C Base basePart hTrans hC hPos hBaseK hHer hKIrr
      hCover hInternal (Set.range e) hTagClosed hTagIrred
  refine ⟨beta, ?_⟩
  intro x
  exact hBeta ⟨e x, ⟨x, rfl⟩⟩

end AllThoseRamseyClasses.Published
