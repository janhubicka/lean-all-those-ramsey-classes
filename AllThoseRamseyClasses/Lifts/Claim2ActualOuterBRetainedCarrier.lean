import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# Every B-active vertex of a genuine selected-Q outer source lies in E

The full-native 2019 right-to-left source replacement constructs a
genuine inserted Q and unchanged complete complement E. Its exact
new outer geometric carrier is the union of ALL Q source vertices
with the images of precisely those E vertices that belonged to the
old outer geometric source piece.

When the inserted Q has NO B-exclusive target image, each new
B-exclusive SOURCE vertex inside the actual new outer piece
necessarily has a UNIQUE retained E representative whose old
full-source image belonged to the original outer piece. The
old/new weak target coordinates on that retained vertex agree.

Conversely every B-exclusive retained E source vertex in the old
outer piece survives inside the new outer piece with its target
coordinate unchanged.

This identifies actual source representatives and avoids counting
distinct weak-target images. It is a useful same-Q bridge from
the selected full-source outer-carrier equation to the
piece-scoped B-boundary injection transfer API.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The no-new-B and exact outer-carrier hypotheses ensure every
new B-exclusive source vertex in the actual outer piece is
uniquely in the retained complete source E, and has a genuine
old outer source representative with exactly the same target.
No target-map injectivity or source forbidden-family premise. -/
theorem fullNativeSelectedOuter_Bactive_unique_retained_source
    {V W QE Q UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L QE} {Replacement : Structure L Q}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT)
    (BActive : Set UT)
    (hCarrier : NewPart =
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart))
    (hNoBFromQ : ∀ q : Q, flip (iNewQ q) ∉ BActive)
    (hEAgree : ∀ e : QE, flip (iNewE e) = f (iOldE e))
    (w : W) (hwPart : w ∈ NewPart) (hwB : flip w ∈ BActive) :
    ∃! e : QE,
      iNewE e = w ∧
      iOldE e ∈ OldPart ∧
      f (iOldE e) = flip w := by
  have hUnion : w ∈
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart) := by
    rw [← hCarrier]
    exact hwPart
  rcases hUnion with ⟨q, _hq, hqMap⟩ | ⟨e, heOld, heMap⟩
  · have hBad : flip (iNewQ q) ∈ BActive := by
      rw [hqMap]
      exact hwB
    exact False.elim ((hNoBFromQ q) hBad)
  · refine ⟨e, ⟨heMap, heOld, ?_⟩, ?_⟩
    · calc
        f (iOldE e) = flip (iNewE e) := (hEAgree e).symm
        _ = flip w := congrArg flip heMap
    · intro e' he'
      exact iNewE.injective (he'.1.trans heMap.symm)

/-- Every old B-exclusive retained-complement source vertex in the
old selected outer carrier appears in the corresponding new outer
carrier and retains its exact target coordinate. -/
theorem fullNativeSelectedOuter_retained_Bactive_survives
    {V W QE Q UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L QE} {Replacement : Structure L Q}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (OldPart : Set V) (NewPart : Set W)
    (f : V → UT) (flip : W → UT)
    (BActive : Set UT)
    (hCarrier : NewPart =
      iNewQ '' (Set.univ : Set Q) ∪
        iNewE '' (iOldE ⁻¹' OldPart))
    (hEAgree : ∀ e : QE, flip (iNewE e) = f (iOldE e))
    (e : QE)
    (heOldPart : iOldE e ∈ OldPart)
    (heOldB : f (iOldE e) ∈ BActive) :
    iNewE e ∈ NewPart ∧ flip (iNewE e) ∈ BActive := by
  constructor
  · rw [hCarrier]
    exact Or.inr ⟨e, heOldPart, rfl⟩
  · rw [hEAgree]
    exact heOldB

end AllThoseRamseyClasses.Lifts
