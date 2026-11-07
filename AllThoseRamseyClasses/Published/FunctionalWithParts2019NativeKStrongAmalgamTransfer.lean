import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKPartiteStrongAmalgam
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKStrongAmalgamation
import PartiteConstruction.Functional.NativeWholePartClosure

/-!
# Track B: strong amalgamation transfers to faithful genuine H_K

An original genuine partial function may contain a DEFINED-empty
value, but our faithful H_K class consists exactly of objects
with native witnesses and NO such independently defined-empty
values. Each full genuine partial embedding between these objects
therefore encodes a full native embedding on the same vertex map.
This is the full counterpart to the earlier original-partial
homomorphism discussion; merely source-defined maps cannot
be used in this conversion.

The previous native theorem supplies a genuine PARTITE
K-amalgam of arbitrary full spans, whose function-output
transversality and exact intersection have already been
proved in the native function language. Reinterpret its
target using the faithful Option(Set) representation.

The result is EXACT genuine part-preserving strong amalgamation
of H_K, with all source/target vertices and root overlap unchanged.
In particular native FreeAmalgamationClass K suffices for
the genuine 2019 strong-amalgamation class hypothesis needed
by the canonical tagged K_H image.

No arbitrary partial structure with defined-empty values is
collapsed, no nonclosed weak map is promoted to full embedding,
and no 2019 local relative K-completion is constructed.
-/

namespace StructuralRamsey.PartialSetStructure.Embedding

universe u v
variable {L : StructuralRamsey.Language.{u}} {V W : Type v}

/-- A FULL genuinely partial Option(Set) embedding, with
independent domain reflection, induces a FULL native total
set-valued-function embedding after forgetting definedness.

This is a faithful map on the ORIGINAL vertices, including
the complete multivalued output fibres. It does not make a
source-defined original-partial map FULL. -/
def toCollapsedNative
    {A : StructuralRamsey.PartialSetStructure L V}
    {B : StructuralRamsey.PartialSetStructure L W}
    (e : StructuralRamsey.PartialSetStructure.Embedding A B) :
    StructuralRamsey.Structure.Embedding
      A.collapseDomain B.collapseDomain where
  toFun := e.toFun
  injective := e.injective
  map_rel_iff := e.map_rel_iff
  map_func := by
    intro F x
    have h := congrArg
      (fun m : Option (Set W) => m.getD ∅)
      (e.map_func F x)
    have hOption :
        ((A.func F x).map
          (StructuralRamsey.Structure.imageSet e.toFun)).getD ∅ =
          StructuralRamsey.Structure.imageSet e.toFun
            ((A.func F x).getD ∅) := by
      cases hA : A.func F x with
      | none =>
          change (∅ : Set W) =
            StructuralRamsey.Structure.imageSet e.toFun (∅ : Set V)
          simp [StructuralRamsey.Structure.imageSet]
      | some U => rfl
    change
      StructuralRamsey.Structure.imageSet e.toFun
        ((A.func F x).getD ∅) =
      (B.func F (e.toFun ∘ x)).getD ∅
    exact hOption.symm.trans h

end StructuralRamsey.PartialSetStructure.Embedding

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Native part-preserving strong amalgamation transfers to the
GENUINE 2019 strong-amalgamation property of the EXACT faithful
H_K class. All original partial sources are represented by
native transversal K-systems on their same vertices, so there
is no loss of defined-empty information and the full
embeddings reflect every function fibre.

The native witness preserves part labels and exact overlap;
the new genuine target is just its faithful native
Option(Set) encoding. -/
theorem nativeKFaithfulH_strongAmalgamation
    (K : Structure.StructureClass.{u,v} (L := L))
    (hStrong : NativeKPartiteStrongAmalgamation2019
      (Parts := Parts) K) :
    GenuinePartiteStrongAmalgamation2019
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) := by
  classical
  intro X Y Z hX hY hZ
    Root partRoot Left partLeft Right partRight
    hRoot hLeft hRight hTrRoot hTrLeft hTrRight sL sR
  obtain ⟨RootN, hRootK, hRootEq, hPartRootEq⟩ := hRoot
  obtain ⟨LeftN, hLeftK, hLeftEq, hPartLeftEq⟩ := hLeft
  obtain ⟨RightN, hRightK, hRightEq, hPartRightEq⟩ := hRight
  subst Root
  subst Left
  subst Right
  subst partRoot
  subst partLeft
  subst partRight
  let eL : Structure.Embedding RootN.toStructure LeftN.toStructure := {
    toFun := sL.1.toFun
    injective := sL.1.injective
    map_rel_iff := sL.1.map_rel_iff
    map_func := by
      intro F xs
      have h := (sL.1.toCollapsedNative).map_func F xs
      simpa only [Structure.toNonemptyPartial_collapseDomain,
        PartialSetStructure.Embedding.toCollapsedNative] using h
  }
  let eR : Structure.Embedding RootN.toStructure RightN.toStructure := {
    toFun := sR.1.toFun
    injective := sR.1.injective
    map_rel_iff := sR.1.map_rel_iff
    map_func := by
      intro F xs
      have h := (sR.1.toCollapsedNative).map_func F xs
      simpa only [Structure.toNonemptyPartial_collapseDomain,
        PartialSetStructure.Embedding.toCollapsedNative] using h
  }
  let nL : FunctionalPartite.Embedding RootN LeftN := {
    toEmbedding := eL
    map_part := by
      intro x
      exact sL.2 x
  }
  let nR : FunctionalPartite.Embedding RootN RightN := {
    toEmbedding := eR
    map_part := by
      intro x
      exact sR.2 x
  }
  obtain ⟨W, hW, TargetN, hTargetK, jL, jR, hAgree, hExact⟩ :=
    hStrong RootN LeftN RightN hRootK hLeftK hRightK nL nR
  letI : Finite W := hW
  let jLPartial : PartPreservingEmbedding
      LeftN.toStructure.toNonemptyPartial LeftN.part
      TargetN.toStructure.toNonemptyPartial TargetN.part :=
    ⟨jL.toEmbedding.toNonemptyPartial, jL.map_part⟩
  let jRPartial : PartPreservingEmbedding
      RightN.toStructure.toNonemptyPartial RightN.part
      TargetN.toStructure.toNonemptyPartial TargetN.part :=
    ⟨jR.toEmbedding.toNonemptyPartial, jR.map_part⟩
  refine ⟨W, hW,
    TargetN.toStructure.toNonemptyPartial, TargetN.part,
    ⟨TargetN, hTargetK, rfl, rfl⟩,
    TargetN.toNonemptyPartial_fibreTransversal,
    jLPartial, jRPartial, ?_, ?_⟩
  · intro x
    change jL (nL x) = jR (nR x)
    exact hAgree x
  · intro a b hab
    change jL a = jR b at hab
    obtain ⟨x, ha, hb⟩ := hExact a b hab
    refine ⟨x, ?_, ?_⟩
    · exact ha
    · exact hb

/-- Genuine native functional FreeAmalgamationClass K is sufficient
for the strong-amalgamation hypothesis of the 2019 faithful H_K
partial-function class. The target is a REAL transversal
functional K-amalgam, not a repaired semi-closed weak source. -/
theorem nativeKFaithfulH_strongAmalgamation_of_free
    (K : Structure.StructureClass.{u,v} (L := L))
    (hK : Structure.FreeAmalgamationClass K) :
    GenuinePartiteStrongAmalgamation2019
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) :=
  nativeKFaithfulH_strongAmalgamation K
    (nativeKPartiteStrongAmalgamation_of_free K hK)

/-- The canonical 2019 full-ROOT-tagged relational image
of a native free-amalgamation class has genuine RELATIONAL
finite strong amalgamation, using exact same-carrier
faithful H_K sources and full part-preserving embeddings.

This DISCHARGES the 2019 canonical K_H strong property
independently of the remaining ambient-relative local
completion axiom and the unrelated strict mixed-root targets. -/
theorem nativeKCanonicalTagged2019_strongAmalgamation_of_free
    (K : Structure.StructureClass.{u,v} (L := L))
    (hK : Structure.FreeAmalgamationClass K) :
    HasFiniteStrongAmalgamation
      (canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)) :=
  canonicalGenuineTagged2019Class_strongAmalgamation
    (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)
      (nativeKFaithfulH_strongAmalgamation_of_free K hK)

end AllThoseRamseyClasses.Published
