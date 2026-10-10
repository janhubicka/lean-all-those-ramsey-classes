import AllThoseRamseyClasses.Published.CorrectedSingletonEscapeBound
import AllThoseRamseyClasses.Published.LiteralCompletionCopywise
import AllThoseRamseyClasses.Published.LiteralCounterexampleAssembly

/-!
# The proposed (4b)-ONLY repair is still vacuous for paired equivalences

This is the crucial second counterexample calculation.

Keep Definition 2.15, (4a) and (4c) COMPLETELY LITERAL.
The ONLY changed condition is corrected (4b), testing the
U-CLOSED U-irreducible substructures for K membership.

The previously proved singleton-escape lemma gives a global bound
  card C <= card C0 + 1
whenever the corrected local antecedent holds.

Take n(B,C0)=card C0+1. The ORIGINAL (4c) tests the whole
weak induced structure C|univ. Its promised original
(K,U)-completion preserves all embedded B-copies, because each
B is ordinarily irreducible and therefore U-irreducible.

Thus this SAME non-Ramsey class satisfies corrected local
finiteness, still conditional only on the already documented
finite strong amalgamation theorem.

No published wording is modified, and no unproved lemma is
introduced as an axiom.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Corrected (4b) still gives a TRIVIAL local-completion axiom:
the required bound can be taken to be |C0|+1, independently of B.
All completion maps are the ORIGINAL 2019 Definition 2.15 maps. -/
theorem finitePairedClass_corrected_local_cutoff
    {VB P : Type} [Finite VB] [Finite P]
    (Base : RelStructure Lang VB)
    (Control : RelStructure Lang P)
    (hBase : finitePairedClass Base) :
    CorrectedULocalCompletionAt finitePairedClass
      mateRules Base Control (Nat.card P + 1) := by
  intro X hX C hClosed hControl hCover hSmall
  have hBound : Nat.card X ≤ Nat.card P + 1 :=
    corrected_cover_literal_control_card_bound
      C Control hClosed hCover hControl
  classical
  letI : Fintype X := Fintype.ofFinite X
  have hUniv : (Finset.univ : Finset X).card ≤ Nat.card P + 1 := by
    simpa [Nat.card_eq_fintype_card] using hBound
  have hCompletion : HasLiteralUKCompletion finitePairedClass mateRules
      (C.induce (↑(Finset.univ : Finset X) : Set X)) :=
    hSmall Finset.univ hUniv
  have hIrred : Base.Irreducible :=
    orderedAmbient_irreducible Base
      (finitePairedClass_subset_orderedAmbient Base hBase)
  let eUniv : Embedding C
      (C.induce (↑(Finset.univ : Finset X) : Set X)) := {
    toFun := fun x => ⟨x, Finset.mem_univ _⟩
    injective := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  exact (hCompletion.toCopywise hIrred).precomp_embedding eUniv

/-- Unlike the original vacuity proof, we now prove corrected
local finiteness for EVERY pair (B,C0), not only one B. -/
theorem finitePairedClass_corrected_local_all
    {VB P : Type} [Finite VB] [Finite P]
    (Base : RelStructure Lang VB)
    (Control : RelStructure Lang P)
    (hBase : finitePairedClass Base) :
    ∃ n : ℕ, CorrectedULocalCompletionAt
      finitePairedClass mateRules Base Control n :=
  ⟨Nat.card P + 1,
    finitePairedClass_corrected_local_cutoff Base Control hBase⟩

/-- Assuming only the still-open strong AP of K, all class-level
hypotheses of the preferred minimally corrected Definition 2.17
hold for this non-Ramsey K. In particular the proof retains the
ORIGINAL (4a) and (4c), not the weaker working map variant. -/
theorem finitePaired_corrected_multiamalgamation_of_strong
    (hStrong : HasFiniteStrongAmalgamation finitePairedClass) :
    MinimallyCorrectedMultiamalgamationClass
      orderedAmbientClass finitePairedClass mateRules := by
  let hLiteral :=
    finitePaired_literal_multiamalgamation_of_strong hStrong
  refine {
    subset := hLiteral.subset
    finite := hLiteral.finite
    closed := hLiteral.closed
    hereditary := hLiteral.hereditary
    strong := hLiteral.strong
    localCompletion := ?_ }
  intro X Y hX hY Base Control hBase _
  exact finitePairedClass_corrected_local_all Base Control hBase

/-- Formal conditional refutation of the preferred one-clause
corrected universal Theorem 2.18. The only remaining premise
in the class counterexample is K's strong amalgamation. -/
theorem correctedTheorem218_implies_not_pairedStrong
    (hPublished : CorrectedTheorem218Target.{0, 0} (L := Lang)) :
    ¬ HasFiniteStrongAmalgamation finitePairedClass := by
  intro hStrong
  have hPackage : MinimallyCorrectedMultiamalgamationClass
      orderedAmbientClass finitePairedClass mateRules :=
    finitePaired_corrected_multiamalgamation_of_strong hStrong
  have hK : FiniteRamseyClass finitePairedClass :=
    hPublished orderedAmbientClass finitePairedClass mateRules
      orderedAmbient_isRamsey
      (fun C hC => orderedAmbient_irreducible C hC)
      hPackage
  exact finitePairedClass_notRamsey hK

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
