import AllThoseRamseyClasses.Lifts.Claim2ActualOuterBActiveCard
import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# Actual geometric selected-inner-piece witness for strict B-source descent

A genuine geometric separator cut has the old complete complement
carrier equal to the complement of the selected nonroot component.
Thus no actual source vertex of that component can come from the
old full-complement embedding.

Combined with exact selected-Q outer carrier reconstruction and
no-new-B Q, ANY old B-active source vertex of the selected inner
component yields a strict B-source count decrease for the actual
new geometric outer piece.

This discharges the "missing old retained source" hypothesis from
Claim2ActualOuterBActiveCard in a genuine source geometry. It does not
provide a selectable one-sided inner piece or handle mixed smaller roots.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The actual FULL native old complement of a selected geometric
piece contains no source vertex of the selected nonroot component.
The weak EHN target map is not involved. -/
theorem geometricSelectedComponent_disjoint_fullOldComplementRange
    {V : Type}
    (Old : Structure L V) {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (x : V)
    (hx : x ∈ functionalComponentFrom Old
      (Set.range inner.roots) inner.left) :
    x ∉ Set.range (functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left) := by
  rintro ⟨e, he⟩
  have hOutside : (e.1 : V) ∉
      functionalComponentFrom Old
        (Set.range inner.roots) inner.left := e.2
  have heq : (e.1 : V) = x := he
  apply hOutside
  rw [heq]
  exact hx

/-- The original geometric outer piece loses at least one
B-active source vertex after a genuine selected-Q replacement
whenever the selected inner component contains such a vertex.

The entire Q plus retained E union must be the ACTUAL new
geometric outer carrier, and Q itself must be B-inactive.
All counts are SOURCE cardinalities. -/
theorem geometricSelectedInnerFlip_Bactive_card_strict
    {V W Q UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {n m : ℕ}
    (outer : GeometricFunctionalPieceData Old n)
    (inner : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old inner ⊆
        geometricPieceVertices Old outer)
    (New : Structure L W)
    (Replacement : Structure L Q)
    (iNewQ : Structure.Embedding Replacement New)
    (iNewE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (newOuter : GeometricFunctionalPieceData New n)
    (f : V → UT) (flip : W → UT) (BActive : Set UT)
    (hCarrier :
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (oldOuterContextInInnerComplement Old outer inner) =
          geometricPieceVertices New newOuter)
    (hNoBFromQ : ∀ q : Q, flip (iNewQ q) ∉ BActive)
    (hEAgree :
      ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
        flip (iNewE e) = f e.1)
    (x : V)
    (hxComponent : x ∈ functionalComponentFrom Old
      (Set.range inner.roots) inner.left)
    (hxB : f x ∈ BActive) :
    Nat.card {w : W // w ∈ geometricPieceVertices New newOuter ∧
      flip w ∈ BActive} <
    Nat.card {v : V // v ∈ geometricPieceVertices Old outer ∧
      f v ∈ BActive} := by
  letI : Finite V := hFiniteOld
  have hFiniteE :
      Finite (geometricGlobalComplementChart Old inner).Carrier :=
    inferInstance
  have hxOuter : x ∈ geometricPieceVertices Old outer :=
    hInnerInside (Or.inr hxComponent)
  have hMissing :
      ∃ v : V, v ∈ geometricPieceVertices Old outer ∧
        f v ∈ BActive ∧
        v ∉ Set.range
          (functionalComponentComplementEmbedding Old
            (Set.range inner.roots) inner.minimal.1 inner.left) :=
    ⟨x, hxOuter, hxB,
      geometricSelectedComponent_disjoint_fullOldComplementRange
        Old inner x hxComponent⟩
  exact fullNativeSelectedOuter_Bactive_card_lt_old_of_missing_retained
    (functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left)
    iNewE iNewQ
    (geometricPieceVertices Old outer)
    (geometricPieceVertices New newOuter)
    f flip BActive hFiniteOld hFiniteE
    hCarrier.symm hNoBFromQ hEAgree hMissing

end AllThoseRamseyClasses.Lifts
