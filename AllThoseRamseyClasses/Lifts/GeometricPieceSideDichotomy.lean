import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor

/-!
# Exact side-containment dichotomy for geometrically selected forbidden pieces

If the entire root cut of a selected geometric piece lies in the
PREIMAGE of the full common amalgam root, then its root vertices
already map into the LEFT witness. Each additional component vertex
maps either left-exclusive, right-exclusive, or to the common root.

Consequently either the entire selected piece maps into the left
side, or the selected component contains a right-exclusive vertex.
In the first case the global original-2019 EHN homomorphism-embedding
of the source factors to an actual weak EHN piece map into Left
using the full target side inclusion.

This is the precise structural dichotomy before Claim 1, and does
NOT prove that the left-side flip exists for colliding root images.
No source map injectivity or reflection of undefined function
inputs is assumed.
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

/-- If a selected geometric piece has all roots in the common
root's preimage and NO right-exclusive vertex in the selected
component, its ENTIRE carrier maps into the left full target side. -/
theorem weakGeometricPiece_leftImage_of_no_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoot : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hNoRight : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f) :
    ∀ z : geometricPieceVertices Source d,
      ∃ a : E, f z.1 = iL a := by
  intro z
  rcases z.2 with hR | hC
  · obtain ⟨r, hr⟩ := hRoot hR
    exact ⟨sL r, hr.symm⟩
  · rcases weakFreePartition_covers hfree f z.1 with hX | hL | hR
    · obtain ⟨r, hr⟩ := hX
      exact ⟨sL r, hr.symm⟩
    · exact hL.1
    · exact False.elim (hNoRight z.1 hC hR)

/-- Either the ENTIRE geometric piece factors through Left at
the level of vertex images, or a concrete right-exclusive
vertex occurs in its chosen component.

Neither branch infers injectivity of the root image. -/
theorem weakGeometricPiece_left_or_component_meets_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoot : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f) :
    (∀ z : geometricPieceVertices Source d,
      ∃ a : E, f z.1 = iL a) ∨
    ∃ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left ∧
      z ∈ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f := by
  classical
  by_cases hNoRight : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f
  · exact Or.inl
      (weakGeometricPiece_leftImage_of_no_right hfree f d
        hRoot hNoRight)
  · right
    by_contra hex
    apply hNoRight
    intro z hz hright
    exact hex ⟨z, hz, hright⟩

/-- The full left-side factorization of a genuine geometrically
selected piece, conditional only on the verified piece containment
criterion. This is the actual EHN interface used by the global
canonical relation and geometric flip lemmas. -/
theorem weakGeometricPiece_factor_left_if_no_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n)
    (hRoot : Set.range d.roots ⊆
      weakFreeRootPart (sL := sL) (iL := iL) f)
    (hNoRight : ∀ z : U,
      z ∈ functionalComponentFrom Source (Set.range d.roots) d.left →
      z ∉ weakFreeRightPart
        (sL := sL) (iL := iL) (iR := iR) f) :
    ∃ pLeft : geometricPieceVertices Source d → E,
      (geometricFunctionalPiece Source d).IsEHNHomomorphismEmbedding
        Left pLeft ∧
      ∀ z, iL (pLeft z) = f z.1 := by
  exact geometricPieceWeakMap_factor_ambient_side
    Source d Whole f hf Left iL
    (weakGeometricPiece_leftImage_of_no_right
      hfree f d hRoot hNoRight)

end AllThoseRamseyClasses.Lifts
