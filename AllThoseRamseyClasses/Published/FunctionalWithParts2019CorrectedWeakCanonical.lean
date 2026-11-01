import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Track C: exact weak ordinary-irreducible tests have genuine H targets

Corrected (4b) does not promise that every test embeds into a single
fixed B: it says each U-closed U-irreducible induced structure belongs
to the canonical relational image of the ORIGINAL functional class H.

Nevertheless every ordinary irreducible weak test on S is contained
in its ambient U-closure hull, which is U-closed and U-irreducible.
Apply (4b) to THAT hull, then restrict the resulting same-carrier
canonical representation to S. The test S itself is not closed or
enlarged; only the auxiliary witness is the larger hull.

This yields a full relational embedding of the exact induced weak
test into a genuine part-labelled Option(Set) H-member. Its target
can depend on S. No fixed Base B or strong amalgamation is used.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Actual (4b) guarantees a canonical genuine H-target for EVERY
ordinary irreducible exact induced weak test on S. The original
vertex carrier S and its full relational relations are preserved
by a full embedding into that H-target's tagged representation. -/
theorem genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (S : Set V) (hIrred : (C.induce S).Irreducible) :
    ∃ (X : Type w) (_ : Finite X)
      (Target : PartialSetStructure L X) (partTarget : X → Parts),
      H Target partTarget ∧ FibreTransversal Target partTarget ∧
      Nonempty (RelStructure.Embedding
        (C.induce S)
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target partTarget))) := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let Hull : Set V := UClosureHull rules C S
  have hHullClosed : IsUClosed rules (C.induce Hull) :=
    hClosed.induce_UClosureHull S
  have hHullIrred : IsUIrreducible rules (C.induce Hull) :=
    hClosed.irreducibleSeed_hull_isUIrreducible S hIrred
  have hHullK : canonicalGenuineTagged2019Class H (C.induce Hull) :=
    hCovered Hull hHullClosed hHullIrred
  obtain ⟨hFinite, Target, partTarget, hTargetH, hTargetTr, hEq⟩ := hHullK
  let e : RelStructure.Embedding (C.induce S) (C.induce Hull) := {
    toFun := fun x => ⟨x.1, subset_UClosureHull rules C S x.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg Subtype.val h
    map_rel_iff := fun _ _ => Iff.rfl
  }
  refine ⟨Hull, hFinite, Target, partTarget, hTargetH, hTargetTr, ?_⟩
  rw [← hEq]
  exact ⟨e⟩

end AllThoseRamseyClasses.Published
