import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGaifman
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamExteriorOldRoot

/-!
# Safe source-complement paths under a genuine functional piece replacement

This module proves an exact source-side path transport useful for the
remaining contextual Claim 2 iteration of the 2019 lift proof.

Suppose an old source is a genuine FULL native functional free amalgam
Old = Inner +_Root Complement. Its root may be incomparable with the
root of an older geometric piece. Two vertices in the complete unchanged
complement can be Gaifman-adjacent in Old because of a relation/function
tuple which is NOT contained in Complement: both endpoints may be in
the gluing Root while another coordinate is in the removed inner piece.

However, if AT LEAST ONE of the two complement vertices lies outside
the gluing Root, the original full-amalgam graph-tuple side lemma
forces the whole witnessing tuple into Complement. The edge reflects
there and therefore survives ANY full embedding of Complement into a
replacement source. No graph-induced-substructure shortcut is used.

We extend this reflection to finite paths with the exact per-edge
private-endpoint property, without asserting (incorrectly) that all
old paths in the complement reflect. The remaining mathematical
obligation is to find these SAFE paths from each retained old
interior vertex to the surviving inner root. The first-root-hitting
construction belongs in a separate lemma. Neither that obligation
nor the entire transported outer geometric piece is supplied here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- An OLD-source Gaifman edge between two complement vertices is already
an edge of the complete unchanged complement if at least one endpoint
is private to that complement (not in the inner gluing root).
This reflection is valid for arbitrary relation and function arities,
including nullary symbols and repeated tuple coordinates. -/
theorem fullFreeAmalgam_safeComplementEdge_reflect
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Old}
    {iComp : Structure.Embedding Complement Old}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (a b : B)
    (hPrivate : a ∉ Set.range sComp ∨ b ∉ Set.range sComp)
    (hOld : GaifmanAdjacent Old.graph (iComp a) (iComp b)) :
    GaifmanAdjacent Complement.graph a b := by
  rcases hPrivate with ha | hb
  · exact
      (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
        hFree a b ha).mp hOld
  · have hReverse :
        GaifmanAdjacent Old.graph (iComp b) (iComp a) :=
      GaifmanAdjacent.symm hOld
    have hCompReverse :
        GaifmanAdjacent Complement.graph b a :=
      (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
        hFree b a hb).mp hReverse
    exact GaifmanAdjacent.symm hCompReverse

/-- A path carried by the unchanged complement survives a genuine
inner replacement when every old-source edge has a complement-private
endpoint. The old source is the FULL functional free amalgam of the
removed piece and its complement. Only a FULL embedding of the same
complement into the new source is needed to transport its paths.

A cut T is an arbitrary set of complement vertices, not necessarily
the inner root; it may be an incomparable older outer separator.
The conclusion is an actual Gaifman path in the NEW source avoiding
the image of the WHOLE cut T. -/
theorem fullFreeAmalgam_safeComplementPath_transfer
    {H E B W W' : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Old}
    {iComp : Structure.Embedding Complement Old}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (jComp : Structure.Embedding Complement New)
    (T : Set B)
    (x y : {b : B // b ∉ T})
    (hSafe : Relation.ReflTransGen
      (fun a b : {z : B // z ∉ T} =>
        (a.1 ∉ Set.range sComp ∨ b.1 ∉ Set.range sComp) ∧
        GaifmanAdjacent Old.graph (iComp a.1) (iComp b.1))
      x y) :
    ReachOutside New.graph (jComp '' T)
      (fullFunctionalEmbedding_outsideCut jComp T x)
      (fullFunctionalEmbedding_outsideCut jComp T y) := by
  have hPath : ReachOutside Complement.graph T x y := by
    induction hSafe with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hpre hedge ih =>
        have hStep : outsideAdjacency Complement.graph T a b :=
          fullFreeAmalgam_safeComplementEdge_reflect
            hFree a.1 b.1 hedge.1 hedge.2
        exact ih.tail hStep
  exact fullFunctionalEmbedding_reachOutside_map jComp T hPath

end AllThoseRamseyClasses.Lifts
