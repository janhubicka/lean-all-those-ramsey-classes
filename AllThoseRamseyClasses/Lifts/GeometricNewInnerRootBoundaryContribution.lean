import AllThoseRamseyClasses.Lifts.GeometricInnerRootOuterBoundary
import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot

/-!
# The actual new inner geometric root generates old-cut boundary vertices

After a full native inner piece replacement, let d be the ACTUAL
new geometrical piece of New and let T be the older, possibly
incomparable, function-closed cut transported through the identical
complete complement. Assume the selected new inner component D'
lies in a new T-component C'.

By the exact geometric minimal-separator equation,
U = Cl_New(N_New(D')), where U is the FULL generated inner root.
The verified subcomponent boundary localization (#745) and its
geometric specialization (#755) imply:
   U intersect T subset Cl_New(N_New(C')).

Here we identify U as the full image of the inner Fin root through
the retained complement's own root embedding. Every shared-root
coordinate lying in T therefore belongs to the GENERATED external
boundary of the new opposite component. No direct edge from that
coordinate to D' is postulated; arbitrary-arity function closure
is preserved.

This is the missing shared-root contribution in the conditional
complete opposite boundary theorem of Track A (#763). It does not
construct the actual new geometric piece; that construction and
outer component identification remain separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- An ACTUAL new inner geometric piece whose full root is the
image of a retained root chart contributes every old-cut root
coordinate to the generated boundary of the new outer component.

Works for arbitrary native partial functions and incomparable
cuts; does not require the weak forbidden target map injective. -/
theorem geometricNewInnerRoot_in_outerGeneratedBoundary
    {H B W : Type v}
    {Root : Structure L H}
    {Complement : Structure L B}
    {New : Structure L W}
    (sComp : Structure.Embedding Root Complement)
    (jComp : Structure.Embedding Complement New)
    (T : Set B) (hTclosed : Complement.IsClosed T)
    (xNew : {w : W // w ∉ jComp '' T})
    {n : ℕ}
    (d : GeometricFunctionalPieceData New n)
    (hInnerRoot :
      Set.range d.roots = jComp '' Set.range sComp)
    (hInnerComponent :
      componentFrom New.graph (Set.range d.roots) d.left ⊆
        componentFrom New.graph (jComp '' T) xNew)
    (r : H) (hrT : sComp r ∈ T) :
    jComp (sComp r) ∈ New.functionClosure
      (gaifmanNeighborhood New.graph
        (componentFrom New.graph (jComp '' T) xNew)) := by
  have hNewTclosed : New.IsClosed (jComp '' T) :=
    functionalEmbedding_image_closed
      Complement New jComp T hTclosed
  have hRootBoundary :=
    geometricInnerRoot_insideOlderCut_generatedByOuterBoundary
      New d (jComp '' T) hNewTclosed xNew hInnerComponent
  have hrRoot : jComp (sComp r) ∈ Set.range d.roots := by
    rw [hInnerRoot]
    exact ⟨sComp r, ⟨r, rfl⟩, rfl⟩
  have hrCut : jComp (sComp r) ∈ jComp '' T :=
    ⟨sComp r, hrT, rfl⟩
  exact hRootBoundary ⟨hrRoot, hrCut⟩

end AllThoseRamseyClasses.Lifts
