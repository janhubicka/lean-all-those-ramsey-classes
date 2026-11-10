import AllThoseRamseyClasses.Published.TrackEActualStandardSystemSparseWitness
import AllThoseRamseyClasses.Published.FunctionalWithParts2019OriginalHypothesesRamsey

/-!
# Track E: conditional class-level Ramsey theorem in native partite System API

The corrected 2019 original-H Ramsey theorem is for truly partial
Option(Set) operations. Native functional partite Systems use set-valued
operations with the faithful nonempty-fibre convention and demand
BOTH function-output and relation-tuple part transversality.

A PARTIAL H-class can contain some ∅-defined operations. Their domain bit
cannot be collapsed faithfully into a native Structure. Thus to deduce a
native class-level conclusion from the existing checked original-H
theorem, explicitly require that every finite H-member has no defined
empty applications. Likewise ordinary H output-fibre transversality
does not by itself imply native relation-tuple transversality; that is
a second explicit premise on H-members.

Subject to exactly these TWO ADDITIONAL class-wide native-fidelity
premises, the already checked corrected 2019 conditional H theorem
transports to the native FunctionalPartite.System API. This requires
the SAME corrected tagged local relative-completion implication as
the upstream 2019 theorem; we do NOT derive that implication here.
The witness is an ACTUAL member of H after faithful re-encoding.

No invalid historical total-domain-reflecting projection or strict
mixed-root functional B-tree argument is used or claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The native-system Ramsey property for the finite H-members whose
genuinely partial encodings lie in H. This uses full embeddings with
the actual parts of EVERY vertex (including isolated vertices). -/
def NativePartite2019FiniteRamsey
    (H : GenuinePartite2019Class (L := L) (Parts := Parts)) : Prop :=
  ∀ {X Y : Type w} [Finite X] [Finite Y]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y),
    H A.toStructure.toNonemptyPartial A.part →
    H B.toStructure.toNonemptyPartial B.part →
    ∀ (κ : Type) [Fintype κ] [Nonempty κ],
      ∃ (Z : Type w) (_ : Finite Z)
        (D : FunctionalPartite.System L Parts Z),
        H D.toStructure.toNonemptyPartial D.part ∧
        FunctionalPartite.Arrow A B D κ

/-- The CORRECTED 2019 conditional class theorem implies an actual
standard native functional partite Ramsey class, when the ORIGINAL
genuine-partial class has no defined-empty fibres and when every
H-member's old relation tuples are transversal on actual vertex parts.

These two extra premises are not consequences of ordinary
FibreTransversal, strong amalgamation or small weak-test completions;
they are necessary to faithfully recover native Systems as H-members
from arbitrary genuine-partial output witnesses. -/
theorem nativePartite2019_ramsey_of_original_hypotheses_and_native_fidelity
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → R E)
    (hPos : L.PositiveFuncArity)
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hLocal : ∀ {X Y : Type w} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C₀ : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class H B → R C₀ →
      ∃ n : ℕ, GenuinePartiteTagged2019LocalCompletionAt H B C₀ n)
    (hNoDefinedEmpty : ∀ {X : Type w} [Finite X]
      (P : PartialSetStructure L X) (part : X → Parts),
      H P part → NoDefinedEmptyValues P)
    (hNativeRelTransversal : ∀ {X : Type w} [Finite X]
      (P : PartialSetStructure L X) (part : X → Parts),
      H P part → NativeRelationTupleTransversal P.collapseDomain part) :
    NativePartite2019FiniteRamsey H := by
  classical
  have hPartial : GenuinePartite2019FiniteRamsey H :=
    genuinePartite2019_ramsey_of_original_functional_hypotheses
      H R hR hRIrred hSub hPos hHer hStrong hIso hLocal
  intro X Y hFinX hFinY A B hHA hHB κ hFinκ hNonemptyκ
  have hTrA : FibreTransversal
      A.toStructure.toNonemptyPartial A.part :=
    (nativeFunctionFibreTransversal_iff_partial
      A.toStructure A.part).mp A.funcTransversal
  have hTrB : FibreTransversal
      B.toStructure.toNonemptyPartial B.part :=
    (nativeFunctionFibreTransversal_iff_partial
      B.toStructure B.part).mp B.funcTransversal
  obtain ⟨Z, hFinZ, P, partP, hHP, hTrP, hPartialArrow⟩ :=
    hPartial A.toStructure.toNonemptyPartial A.part
      B.toStructure.toNonemptyPartial B.part
      hHA hHB hTrA hTrB κ
  letI : Finite Z := hFinZ
  have hNormal : NoDefinedEmptyValues P :=
    hNoDefinedEmpty P partP hHP
  have hRel : NativeRelationTupleTransversal P.collapseDomain partP :=
    hNativeRelTransversal P partP hHP
  have hFunc : NativeFunctionFibreTransversal P.collapseDomain partP :=
    nativeFunctionFibreTransversal_of_noDefinedEmpty
      P partP hNormal hTrP
  let D : FunctionalPartite.System L Parts Z :=
    sameCarrierFunctionalPartiteSystem P.collapseDomain partP hRel hFunc
  have hNativeArrow : NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part
      P.collapseDomain partP κ :=
    (nativePartPreservingArrow_iff_partialTarget_of_noDefinedEmpty
      A.toStructure A.part B.toStructure B.part
      P partP κ hNormal).mpr hPartialArrow
  have hStandardArrow : FunctionalPartite.Arrow A B D κ :=
    (nativeArrow_iff_standardArrow_of_sameCarrierTransversal
      A B P.collapseDomain partP hRel hFunc κ).mp hNativeArrow
  have hRoundtrip : P.collapseDomain.toNonemptyPartial = P :=
    (noDefinedEmpty_iff_nativeRoundtrip P).mp hNormal
  have hNativeH : H D.toStructure.toNonemptyPartial D.part := by
    change H P.collapseDomain.toNonemptyPartial partP
    rw [hRoundtrip]
    exact hHP
  exact ⟨Z, hFinZ, D, hNativeH, hStandardArrow⟩

end AllThoseRamseyClasses.Published
