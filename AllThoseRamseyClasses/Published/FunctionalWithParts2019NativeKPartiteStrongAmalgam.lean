import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKClosedHeredity
import PartiteConstruction.Functional.WeakAttachment
import PartiteConstruction.Functional.WeakOperations

/-!
# Track B: genuine native PARTITE strong amalgamation from full free amalgamation

The corrected 2019 canonical H_K class needs finite strong
amalgamation of its genuine part-preserving partial-function objects.

First do the native geometric part honestly: two actual finite
transversal functional partite K-systems over FULL PART-PRESERVING
root embeddings have a native transversal K-amalgam with
EXACT intersection. The construction uses the verified genuine
functional `Attachment.attach`, not a quotient of relational
shadow pictures. It relies on the existing native
`Structure.FreeAmalgamationClass K` closure axiom.

The left root image S is native function-closed because it is the
range of a FULL native function embedding. The right root embedding
then determines a FULL partite map f:(Left|S) → Right, obtained by
cancelling the first root embedding through its closed range.
Attach Left as one copy to the core Right along f.

All function fibres and vertex parts are preserved and reflected
on each side; the overlap is literally the common root and has
no additional identifications. This theorem is entirely native
and does not make a nonclosed weak inclusion full.

A separate subsequent lemma will transfer this statement to the
faithful original H_K Option(Set) class using full embedding
faithfulness; the source dependency pin must not be silently changed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v
variable {L : Language.{u}} {Parts : Type v}

/-- Native strong part-preserving amalgamation for genuine transversal
K-systems with the EXACT source-root overlap and complete full
embeddings. K-membership is for the native functional structures;
the output system retains its genuine transversal parts. -/
def NativeKPartiteStrongAmalgamation2019
    (K : Structure.StructureClass.{u,v} (L := L)) : Prop :=
  ∀ {X Y Z : Type v} [Finite X] [Finite Y] [Finite Z]
    (Root : FunctionalPartite.System L Parts X)
    (Left : FunctionalPartite.System L Parts Y)
    (Right : FunctionalPartite.System L Parts Z),
      K Root.toStructure → K Left.toStructure →
      K Right.toStructure →
      ∀ (sL : FunctionalPartite.Embedding Root Left)
        (sR : FunctionalPartite.Embedding Root Right),
      ∃ (W : Type v) (_ : Finite W)
        (Target : FunctionalPartite.System L Parts W),
        K Target.toStructure ∧
        ∃ (jL : FunctionalPartite.Embedding Left Target)
          (jR : FunctionalPartite.Embedding Right Target),
          (∀ x : X, jL (sL x) = jR (sR x)) ∧
          (∀ a : Y, ∀ b : Z, jL a = jR b →
            ∃ x : X, a = sL x ∧ b = sR x)

/-- Full native free amalgamation yields genuine native PARTITE
strong amalgamation: glue the right core to one left copy over
the closed literal range of the FULL left root embedding.

The part map on the new system is the one supplied by the
already verified transversal functional attachment, and overlap
follows from the actual `unit_isFreeAmalgam.overlap` field.
No artificial part quotient, temporary multivalued state or
extra intrinsic weak source is introduced. -/
theorem nativeKPartiteStrongAmalgamation_of_free
    (K : Structure.StructureClass.{u,v} (L := L))
    (hK : Structure.FreeAmalgamationClass K) :
    NativeKPartiteStrongAmalgamation2019 (Parts := Parts) K := by
  classical
  intro X Y Z hX hY hZ Root Left Right hRoot hLeft hRight sL sR
  let S : Set Y := Set.range sL.toEmbedding.toFun
  have hS : Left.toStructure.IsClosed S :=
    sL.toEmbedding.range_isClosed
  let inc : Structure.Embedding
      (Left.toStructure.induce S hS) Left.toStructure :=
    Structure.inclusion Left.toStructure S hS
  have hRange : ∀ x : S, ∃ a : X, inc x = sL.toEmbedding a := by
    intro x
    obtain ⟨a, ha⟩ := x.2
    exact ⟨a, ha.symm⟩
  let gNative : Structure.Embedding
      (Left.toStructure.induce S hS) Root.toStructure :=
    inc.factorThroughClosedRange sL.toEmbedding hRange
  have hgSpec (x : S) :
      sL (gNative x) = x.1 := by
    exact (inc.factorThroughClosedRange_spec
      sL.toEmbedding hRange x)
  let g : FunctionalPartite.Embedding (Left.induce S hS) Root := {
    toEmbedding := gNative
    map_part := by
      intro x
      calc
        Root.part (gNative x) =
            Left.part (sL (gNative x)) :=
          (sL.map_part (gNative x)).symm
        _ = Left.part x.1 := congrArg Left.part (hgSpec x)
  }
  let f : FunctionalPartite.Embedding (Left.induce S hS) Right :=
    sR.comp g
  let maps : PUnit.{v+1} →
      FunctionalPartite.Embedding (Left.induce S hS) Right :=
    fun _ => f
  let Target :=
    FunctionalPartite.Attachment.attach Left S hS Right maps
  let jL : FunctionalPartite.Embedding Left Target :=
    FunctionalPartite.Attachment.copyEmbedding Left S hS Right maps PUnit.unit
  let jR : FunctionalPartite.Embedding Right Target :=
    FunctionalPartite.Attachment.coreEmbedding Left S hS Right maps
  have hTarget : K Target.toStructure :=
    FunctionalPartite.Attachment.unit_mem Left S hS Right f
      hK hLeft hRight
  refine ⟨_, inferInstance, Target, hTarget, jL, jR, ?_, ?_⟩
  · intro a
    let s : S := ⟨sL a, ⟨a, rfl⟩⟩
    have hgs : gNative s = a :=
      sL.toEmbedding.injective (by
        calc
          sL (gNative s) = s.1 := hgSpec s
          _ = sL a := rfl)
    have hfs : f s = sR a := by
      change sR (gNative s) = sR a
      rw [hgs]
    calc
      jL (sL a) = jR (f s) := by
        exact FunctionalPartite.Attachment.copy_extends
          Left S hS Right maps PUnit.unit s
      _ = jR (sR a) := congrArg jR hfs
  · intro a b hab
    have hFree :
        Structure.IsFreeAmalgam
          f.toEmbedding (Structure.inclusion Left.toStructure S hS)
          jR.toEmbedding jL.toEmbedding :=
      Structure.Attachment.unit_isFreeAmalgam
        Left.toStructure S hS Right.toStructure f.toEmbedding
    obtain ⟨s, hB, hA⟩ :=
      (hFree.overlap b a).mp hab.symm
    obtain ⟨x, hx⟩ := s.2
    have hgs : gNative s = x :=
      sL.toEmbedding.injective (by
        calc
          sL (gNative s) = s.1 := hgSpec s
          _ = sL x := hx.symm)
    refine ⟨x, ?_, ?_⟩
    · exact hA.trans hx.symm
    · calc
        b = f s := hB
        _ = sR (gNative s) := rfl
        _ = sR x := congrArg sR hgs

end AllThoseRamseyClasses.Published
