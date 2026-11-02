import AllThoseRamseyClasses.Published.FunctionalWithParts2019TotalUnaryCovered
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedIntrinsicLocalTransfer

/-!
# Track C: ambient OLD H-completion exists, but NO full intrinsic H-completion

This strengthens the total-unary regression to use the WHOLE repaired
class antecedent. The original two-vertex total unary H-source has:
  * a canonical tagged K(H) member, hence U-closed and (4b)-covered;
  * a 2-vertex ordinarily irreducible canonical tagged target, so
    the exact ambient-induced S={0} OLD test has a corrected relative
    K(H)-completion via the literal inclusion;
  * NO full genuine partial-function embedding of the intrinsic
    whole-fibre weak singleton into ANY H-member, because it deletes
    F(0) while H demands F defined everywhere.

Thus even U-closedness + actual corrected (4b) + existence of an
ambient relative completion do NOT supply a full intrinsic weak
H-completion. The condition being contrasted is a SINGLE exact
local certificate, not the full outer local-class implication.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

private def inputPattern :
    Language.FunctionInputPattern (exampleLanguage.withParts (Fin 2)) where
  symbol := ULift.up ()
  rootSize := 1
  argMap := fun _ => 0
  onto := by
    intro i
    exact ⟨0, Subsingleton.elim (0 : Fin 1) i⟩

private def outputMask : Language.CompleteOutputParts (Fin 2) :=
  ⟨⟨(1 : Fin 3), (fun _ : Fin 1 => (1 : Fin 2))⟩,
   by intro i j _; exact Subsingleton.elim i j⟩

private def edgeTuple : Fin (inputPattern.rootSize + outputMask.size) → Fin 2 :=
  Fin.append (fun _ : Fin 1 => (0 : Fin 2))
    (fun _ : Fin 1 => (1 : Fin 2))

/-- A complete OLD value tuple connects both distinct vertices 0 and
1, so the two-point original tagged H-member is irreducible. -/
private theorem tagged_edge :
    (wholeMaskTagExpansion
      (withPartsWholeMaskOld totalUnaryToy (fun x : Fin 2 => x))).rel
      (.inl (.inr (.inr (inputPattern,outputMask)))) edgeTuple := by
  change
    Function.Injective (fun _ : Fin 1 => (0 : Fin 2)) ∧
    some ({(1 : Fin 2)} : Set (Fin 2)) =
      some (Set.range (fun _ : Fin 1 => (1 : Fin 2))) ∧
    (∀ j : Fin 1, (1 : Fin 2) = (1 : Fin 2))
  refine ⟨fun i j _ => Subsingleton.elim i j, ?_, fun _ => rfl⟩
  congr 1
  ext x
  simp

private theorem tagged_irreducible :
    (wholeMaskTagExpansion
      (withPartsWholeMaskOld totalUnaryToy (fun x : Fin 2 => x))).Irreducible := by
  intro x y hxy
  fin_cases x <;> fin_cases y
  · exact (hxy rfl).elim
  · exact ⟨.inl (.inr (.inr (inputPattern,outputMask))),
      edgeTuple, 0, 1, tagged_edge, rfl, rfl⟩
  · exact ⟨.inl (.inr (.inr (inputPattern,outputMask))),
      edgeTuple, 1, 0, tagged_edge, rfl, rfl⟩
  · exact (hxy rfl).elim

private def weakS : Set (Fin 2) := {(0 : Fin 2)}

/-- The exact AMBIENT 2019 tagged weak singleton has a genuine H-valued
relative completion, preserving its original induced OLD domain bit.
Target and carrier of the witness are explicit: the original
irreducible two-vertex tagged source. -/
theorem totalUnaryToy_ambientRelative_H_completion :
    HasGenuinePartiteTagged2019RelativeCompletion
      totalUnaryPartiteH
      ((wholeMaskTagExpansion
        (withPartsWholeMaskOld totalUnaryToy
          (fun x : Fin 2 => x))).induce weakS) := by
  let C := wholeMaskTagExpansion
    (withPartsWholeMaskOld totalUnaryToy (fun x : Fin 2 => x))
  let f : weakS → Fin 2 := Subtype.val
  have hEmbedding : RelStructure.Embedding (C.induce weakS) C :=
    inclusion C weakS
  have hProtected : IsInducedClosedUHomomorphismEmbedding
      ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2))
      (C.induce weakS) C f :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (hEmbedding.isClosedUHomomorphismEmbedding
        ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2)))
  exact ⟨Fin 2, inferInstance, totalUnaryToy,
    (fun x : Fin 2 => x),
    totalUnaryToy_mem, totalUnaryToy_transversal,
    tagged_irreducible, f, hProtected⟩

/-- Class-relative exact separation with NO target-choice loophole:
the AMBIENT weak test can be completed in H, and the INTRINSIC
whole-weak test cannot be FULLY completed in H, even though the
ambient original source is a true U-closed (4b)-covered K-member. -/
theorem totalUnaryToy_relative_but_no_full_intrinsic_H_completion :
    HasGenuinePartiteTagged2019RelativeCompletion
      totalUnaryPartiteH
      ((wholeMaskTagExpansion
        (withPartsWholeMaskOld totalUnaryToy
          (fun x : Fin 2 => x))).induce weakS) ∧
    (∀ {X : Type}
      (Target : PartialSetStructure exampleLanguage X)
      (partTarget : X → Fin 2),
      totalUnaryPartiteH Target partTarget →
      ¬ Nonempty (PartialSetStructure.Embedding
        (wholeWeakInduce totalUnaryToy weakS) Target)) := by
  refine ⟨totalUnaryToy_ambientRelative_H_completion, ?_⟩
  intro X Target partTarget hTotal
  exact totalUnaryToy_singleton_no_full_H_completion
    Target partTarget hTotal

/-- Stronger than the singleton case: EVERY exact ambient-induced
weak vertex set of the canonical total-unary two-point source has a
genuine H-relative completion into the SAME two-point target.
The full tagged inclusion is a corrected U-homomorphism-embedding.
Neither the test carrier nor its part labels are enlarged. -/
theorem totalUnaryToy_every_ambientRelative_H_completion
    (S : Set (Fin 2)) :
    HasGenuinePartiteTagged2019RelativeCompletion totalUnaryPartiteH
      ((wholeMaskTagExpansion
        (withPartsWholeMaskOld totalUnaryToy
          (fun x : Fin 2 => x))).induce S) := by
  let C := wholeMaskTagExpansion
    (withPartsWholeMaskOld totalUnaryToy (fun x : Fin 2 => x))
  let f : S → Fin 2 := Subtype.val
  have hEmbedding : RelStructure.Embedding (C.induce S) C :=
    inclusion C S
  have hProtected : IsInducedClosedUHomomorphismEmbedding
      ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2))
      (C.induce S) C f :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (hEmbedding.isClosedUHomomorphismEmbedding
        ((exampleLanguage.withParts (Fin 2)).wholeMaskClosureRules (Fin 2)))
  exact ⟨Fin 2, inferInstance, totalUnaryToy,
    (fun x : Fin 2 => x),
    totalUnaryToy_mem, totalUnaryToy_transversal,
    tagged_irreducible, f, hProtected⟩

/-- An exact finite class-relative counterexample to a tempting
pointwise strengthening of the local-axiom transfer: every ambient
induced weak test has an H-valued 2019 completion, while the one
intrinsic weak singleton cannot FULLY embed in any member of H.

This demonstrates a failure of the ALL-TESTS premise conversion, not
of the outer local-finiteness implication, whose consequent can
still hold even when its antecedent is stronger. -/
theorem totalUnaryToy_all_ambient_but_not_all_full_intrinsic :
    (∀ S : Set (Fin 2),
      HasGenuinePartiteTagged2019RelativeCompletion
        totalUnaryPartiteH
        ((wholeMaskTagExpansion
          (withPartsWholeMaskOld totalUnaryToy
            (fun x : Fin 2 => x))).induce S)) ∧
    ¬ (∀ S : Set (Fin 2),
      ∃ (X : Type) (_ : Finite X)
        (Target : PartialSetStructure exampleLanguage X)
        (partTarget : X → Fin 2),
        totalUnaryPartiteH Target partTarget ∧
        Nonempty (PartialSetStructure.Embedding
          (wholeWeakInduce totalUnaryToy S) Target)) := by
  refine ⟨totalUnaryToy_every_ambientRelative_H_completion, ?_⟩
  intro hAll
  let S : Set (Fin 2) := {(0 : Fin 2)}
  obtain ⟨X, hFinite, Target, partTarget, hH, hFull⟩ := hAll S
  exact totalUnaryToy_singleton_no_full_H_completion
    Target partTarget hH hFull

end AllThoseRamseyClasses.Published
