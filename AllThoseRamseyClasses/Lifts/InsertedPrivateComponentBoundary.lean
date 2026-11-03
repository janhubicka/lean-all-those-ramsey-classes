import AllThoseRamseyClasses.Lifts.FullFunctionalFreeAmalgamSwap
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamExteriorOldRoot

/-!
# The inserted private side is an ACTUAL component with its full generated root

In the published 2019 lift flip, the NEW forbidden source is the
complete native functional free amalgam of a selected replacement
extension Q and the original unchanged complement over the shared
full root. The verified exterior component theorem treats the
right side. Applying it to the swapped diagram gives the precise
left-private component statement needed here.

Provided the selected private component of Q has its entire
function-generated external boundary equal to the full root
`Set.range sQ`, it remains EXACTLY a component of the whole
replacement source outside the transported full root, and its
entire generated boundary remains that full root. Neither
connectedness nor any relation/function incidence is inferred
from an induced graph shortcut.

This lemma does not derive the left-boundary hypothesis from
a selected geometric certificate. That separate isomorphism
transport is the next Track A obligation; it must use the
SAME Q returned by the canonical relation and source flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A whole generated-root component on the INSERTED left side
survives the literal native full functional gluing as an exact
whole-source component. Its full generated Gaifman boundary is
the exact image of the old left root (not merely a subset).
The result admits all native relation and function arities. -/
theorem fullFreeAmalgam_insertedPrivateComponent_exactBoundary
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Whole : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Whole}
    {iComp : Structure.Embedding Complement Whole}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (d : {e : E // e ∉ Set.range sInner})
    (hInnerBoundary :
      Inner.functionClosure
        (gaifmanNeighborhood Inner.graph
          (componentFrom Inner.graph (Set.range sInner) d)) =
        Set.range sInner) :
    componentFrom Whole.graph (iInner '' Set.range sInner)
      (fullFunctionalEmbedding_outsideCut iInner
        (Set.range sInner) d) =
        iInner '' componentFrom Inner.graph (Set.range sInner) d ∧
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (iInner '' componentFrom Inner.graph
            (Set.range sInner) d)) =
        iInner '' Set.range sInner := by
  have hSwapped :
      Structure.IsFreeAmalgam sComp sInner iComp iInner :=
    fullFunctionalFreeAmalgam_swap hFree
  exact fullFreeAmalgam_exteriorComponent_preserved_at_oldRoot
    hSwapped (Set.range sInner) d
    (by
      intro e he
      exact he.1)
    hInnerBoundary

end AllThoseRamseyClasses.Lifts
