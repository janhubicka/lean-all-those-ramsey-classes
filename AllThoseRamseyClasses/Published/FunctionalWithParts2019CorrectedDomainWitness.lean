import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedDefinedEmpty
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredValueCoherence
import PartiteConstruction.Functional.WholeMaskPositiveDomainCompletion2019
import PartiteConstruction.Functional.WholeMaskPartialDecode2019

/-!
# Track C: corrected (4b) forces the exact OLD domain/definedness dictionary

An arbitrary U-closed tagged candidate C satisfying the ACTUAL
corrected closed U-irreducible class-membership clause (4b) need not
itself belong to H. Still, every ordinary irreducible exact weak test
has a full canonical H target, possibly depending on the test.

This gives injective OLD active domain roots, and the preceding
Track C theorem gives a complete zero-output OLD graph record.
Positive-output domain masks are completed using the verified 2019
full-root U-closure theorem and the newly derived tag normality.

Consequently, for POSITIVE primitive arity, the genuinely partial
whole-mask decoder is defined at a tuple precisely when the ambient
OLD domain record says so. The positive/negative domain distinction
survives, including defined-empty. No fixed B-cover, enlargement
of the tested weak carrier, or hLocal assumption is needed.

This is a SOURCE-SIDE normalization theorem. It does not assert
that all intrinsic weak substructures retain the ambient domain
record, or that the decoded global C belongs to H.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Every OLD input root of an active function-domain mask is injective
when corrected (4b) holds on a U-closed tagged candidate. The
canonical target is permitted to depend on this exact root. -/
theorem genuineTagged2019_correctedCovered_activeDomain_injective
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (p : Language.FunctionInputPattern (L.withParts Parts))
    (q : Language.CompleteOutputParts Parts)
    (root : Fin p.rootSize → V)
    (hDom : (wholeMaskTagReduct C).rel
      (.inr (.inl (p,q))) root) :
    Function.Injective root := by
  classical
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q)))) root hDom
  obtain ⟨X, hX, Target, partTarget, _, _, ⟨g⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hX
  let rootS : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hDomB :
      ((Target.withParts partTarget).wholeMaskPatternGraph partTarget).rel
        (.inr (.inl (p,q))) (g ∘ rootS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rootS).mpr hDom
  have hInjB : Function.Injective (g ∘ rootS) := hDomB.1
  intro i j hij
  apply hInjB
  exact congrArg g (Subtype.ext hij)

/-- Under corrected (4b), every active OLD domain mask at a
positive-arity function input has a complete output-value witness.
The defined-empty and positive-output cases are kept separate. -/
theorem genuineTagged2019_correctedCovered_domain_has_wholeMaskValue
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (F : (L.withParts Parts).FuncSymbol)
    (x : Fin ((L.withParts Parts).funcArity F) → V)
    (hDom : HasWholeMaskDomain (wholeMaskTagReduct C) F x) :
    ∃ U : Set V,
      HasWholeMaskValue (wholeMaskTagReduct C) F x U := by
  classical
  obtain ⟨m, r, hr, q, root, hActive, hArgs⟩ := hDom
  let pat : Language.FunctionInputPattern (L.withParts Parts) :=
    ⟨F, m, r, hr⟩
  have hInj : Function.Injective root :=
    genuineTagged2019_correctedCovered_activeDomain_injective
      H C hClosed hCovered pat q root hActive
  have hmPos : 0 < m := by
    by_contra h
    have hZero : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact Fin.elim0 (r ⟨0, (hPos.withParts) F⟩)
  by_cases hq0 : q.size = 0
  · obtain ⟨t, hGraph, hRoot⟩ :=
      genuineTagged2019_correctedCovered_definedEmpty_has_completeGraph
        H C hClosed hCovered pat q hq0 root hActive
    refine ⟨Set.range (fun j : Fin q.size =>
      t (Fin.natAdd m j)), m, r, hr, q, t, hGraph, ?_, rfl⟩
    intro i
    calc
      x i = root (r i) := hArgs i
      _ = t (Fin.castAdd q.size (r i)) := (hRoot (r i)).symm
  · have hqPos : 0 < q.size := Nat.pos_of_ne_zero hq0
    have hNormal : WholeMaskTagNormal C :=
      genuineTagged2019_correctedCovered_tagNormal
        H C hClosed hCovered
    obtain ⟨t, hGraph, hRoot⟩ :=
      hNormal.positiveDomain_has_completeValue
        C hClosed pat q hmPos hqPos root hInj hActive
    refine ⟨Set.range (fun j : Fin q.size =>
      t (Fin.natAdd m j)), m, r, hr, q, t, hGraph, ?_, rfl⟩
    intro i
    calc
      x i = root (r i) := hArgs i
      _ = t (Fin.castAdd q.size (r i)) := (hRoot (r i)).symm

/-- EXACT domain reflection for the independently represented
genuine Option(Set) decoder of a U-closed, corrected-(4b)-covered
tagged candidate, at all positive-arity primitive inputs.
The original actual H-class need not contain the whole candidate. -/
theorem genuineTagged2019_correctedCovered_decoder_defined_iff_OLD_domain
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (F : (L.withParts Parts).FuncSymbol)
    (x : Fin ((L.withParts Parts).funcArity F) → V) :
    (wholeMaskTagReduct C).wholeMaskPartialDecode.Defined F x ↔
      HasWholeMaskDomain (wholeMaskTagReduct C) F x := by
  classical
  let E := wholeMaskTagReduct C
  have hUnique : HasUniqueWholeMaskValues E :=
    genuineTagged2019_correctedCovered_uniqueCompleteValues
      H C hClosed hCovered hPos
  have hValid : HasValidCompleteMaskDomains E :=
    genuineTagged2019_correctedCovered_validCompleteMaskDomains
      H C hClosed hCovered
  constructor
  · rintro ⟨U, hSome⟩
    have hValue : HasWholeMaskValue E F x U :=
      (E.wholeMaskPartialDecode_func_some_iff F x hUnique U).mp hSome
    exact hValid.domain_of_value E F x U hValue
  · intro hDom
    obtain ⟨U, hValue⟩ :=
      genuineTagged2019_correctedCovered_domain_has_wholeMaskValue
        H C hClosed hCovered hPos F x hDom
    refine ⟨U, ?_⟩
    exact (E.wholeMaskPartialDecode_func_some_iff F x hUnique U).mpr hValue

end AllThoseRamseyClasses.Published
