import AllThoseRamseyClasses.Lifts.GeometricPieceSideDichotomy

/-!
# Right-side EHN factorization of genuine geometric forbidden pieces

The verified source-piece side dichotomy includes the actual
full left-side EHN factorization, even when the original weak
forbidden-source map is not injective.

Here is the exact RIGHT-hand counterpart. If every source
vertex in the selected nonroot Gaifman component is NOT
left-exclusive and every selected root vertex maps into the
shared full functional root, the WHOLE piece maps into Right.

The generic checked cancellation theorem for EHN maps through
a FULL target embedding then returns an actual piece-level EHN
homomorphism-embedding into Right, preserving native relation
reflection on irreducible tests and complete old function fibres.

In particular, when the selected component is exactly one
RIGHT-exclusive source-minus-shared-root component, its
piece admits such a right factorization. This is the
source-side one-sided condition needed before a canonical
piece flip can be considered. Root-image injectivity and
the common full lift remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- A genuine source piece rooted in the common seam whose
selected component contains no left-exclusive source vertex
has its entire image in the full RIGHT target side.

The root representation uses exact free-amalgam agreement,
not an assumed equality of distinct root coordinates. -/
theorem weakGeometricPiece_rightImage_of_no_left
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoot : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hNoLeft : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := sL) (iL := iL) f) :
    ∀ z : geometricPieceVertices Source d,
      ∃ b : F, f z.1 = iR b := by
  intro z
  rcases z.2 with hzRoot | hzComp
  · obtain ⟨r, hr⟩ := hRoot hzRoot
    have hAgree : iL (sL r) = iR (sR r) :=
      (hfree.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩
    exact ⟨sR r, hr.symm.trans hAgree⟩
  · rcases weakFreePartition_covers hfree f z.1 with hX | hL | hR
    · obtain ⟨r, hr⟩ := hX
      have hAgree : iL (sL r) = iR (sR r) :=
        (hfree.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩
      exact ⟨sR r, hr.symm.trans hAgree⟩
    · exact False.elim (hNoLeft z.1 hzComp hL)
    · exact hR.1

/-- Literal RIGHT-side EHN factorization of a source-attached
geometric piece with a one-sided image. The original witness
map may be arbitrarily noninjective away from its
irreducible full source tests. -/
theorem weakGeometricPiece_factor_right_if_no_left
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoot : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hNoLeft : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := sL) (iL := iL) f) :
    ∃ pRight : geometricPieceVertices Source d → F,
      (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
        Right pRight ∧
      ∀ z, iR (pRight z) = f z.1 := by
  exact geometricPieceWeakMap_factor_ambient_side
    Source d Whole f hf Right iR
    (weakGeometricPiece_rightImage_of_no_left
      hfree f d hRoot hNoLeft)

/-- If the selected component of a genuine root-in-S piece
is EXACTLY the source Gaifman component of a right-exclusive
vertex after deleting the full shared-root preimage S,
the verified monochromatic component theorem excludes all
left-exclusive vertices. Consequently the entire source
piece has a full RIGHT EHN factorization.

No minimal-separator existence is smuggled into this theorem:
d is a real geometric piece supplied as an argument. -/
theorem weakGeometricPiece_factor_right_of_exactSharedRootComponent
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (x : {z : U // z ∉
      weakFreeRootPart (sL := sL) (iL := iL) f})
    (hxRight : x.1 ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (hComp :
      functionalComponentFrom Source (Set.range d.roots) d.left =
      functionalComponentFrom Source
        (weakFreeRootPart (sL := sL) (iL := iL) f) x) :
    ∃ pRight : geometricPieceVertices Source d → F,
      (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
        Right pRight ∧
      ∀ z, iR (pRight z) = f z.1 := by
  have hNoLeft : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := sL) (iL := iL) f := by
    intro z hzComp hzLeft
    have hzRight : z ∈
      weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f :=
      weakFreePartition_component_right hfree f hf.1 x hxRight
        (hComp ▸ hzComp)
    exact (Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hfree f)) hzLeft hzRight
  exact weakGeometricPiece_factor_right_if_no_left
    hfree f hf d hRoots hNoLeft

end AllThoseRamseyClasses.Lifts
