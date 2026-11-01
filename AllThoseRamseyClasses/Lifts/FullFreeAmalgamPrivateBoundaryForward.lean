import AllThoseRamseyClasses.Lifts.FullFreeAmalgamNewOuterConfinement

/-!
# The right-private part of the OLD outer boundary survives a full inner flip

Let Old be a genuine FULL functional free amalgam of an inner
piece and a complete retained Complement; let New contain a FULL
embedding of this same complement. The inner cut U and the older
cut T need not be nested.

Suppose all retained Complement vertices lying in the old outer
T-component are transported into one new outer T-component.
Then every boundary vertex t in T which is PRIVATE to the
Complement (outside the inner gluing root U), and is an actual
Gaifman neighbour of the old T-component, remains an actual
neighbour of that new component.

The key lemma is SOURCE tuple-safe: an edge touching a complement-
private t is necessarily witnessed completely inside Complement.
Thus its other endpoint comes from Complement, and the COMPLETE
native functional incidence survives the full embedding into New.

This treats the t outside U boundary case. The t inside U case
requires a separate generated-root/closure argument (Track A #755).
No complete generated-boundary equality is asserted here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every OLD outer boundary neighbour private to the retained
functional complement remains a NEW boundary neighbour, provided
the retained old outer component is mapped into the chosen new one.

All interfaces are FULL native SOURCE embeddings, so the conclusion
covers arbitrary relation and function arities, including graph
incidences arising from set-valued partial functions. -/
theorem fullFreeAmalgam_rightPrivateOldBoundary_neighbour_survives
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
    (hOld : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (jComp : Structure.Embedding Complement New)
    (T : Set B)
    (xOld : {w : W // w ∉ iComp '' T})
    (xNew : {w : W' // w ∉ jComp '' T})
    (hRetained :
      ∀ b : B,
        iComp b ∈ componentFrom Old.graph (iComp '' T) xOld →
        jComp b ∈ componentFrom New.graph (jComp '' T) xNew)
    (t : B) (htInT : t ∈ T)
    (htPrivate : t ∉ Set.range sComp)
    (hOldNeighbour :
      iComp t ∈ gaifmanNeighborhood Old.graph
        (componentFrom Old.graph (iComp '' T) xOld)) :
    jComp t ∈ gaifmanNeighborhood New.graph
      (componentFrom New.graph (jComp '' T) xNew) := by
  obtain ⟨_, w, hwOld, hOldEdge⟩ := hOldNeighbour
  have hReversed : GaifmanAdjacent Old.graph (iComp t) w :=
    GaifmanAdjacent.symm hOldEdge
  obtain ⟨b, hbImage⟩ :=
    fullFreeAmalgam_rightPrivate_neighbor_in_right
      hOld t htPrivate w hReversed
  have hbOld :
      iComp b ∈ componentFrom Old.graph (iComp '' T) xOld := by
    rw [hbImage]
    exact hwOld
  have hbNew :
      jComp b ∈ componentFrom New.graph (jComp '' T) xNew :=
    hRetained b hbOld
  have hRightEdge : GaifmanAdjacent Complement.graph t b :=
    (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
      hOld t b htPrivate).mp (by
        rw [hbImage]
        exact hReversed)
  have hNewEdge : GaifmanAdjacent New.graph (jComp b) (jComp t) :=
    fullFunctionalEmbedding_gaifmanEdge_map jComp
      (GaifmanAdjacent.symm hRightEdge)
  have hNotNewComponent :
      jComp t ∉ componentFrom New.graph (jComp '' T) xNew := by
    intro hMember
    exact (Set.disjoint_left.mp
      (componentFrom_disjoint_cut New.graph (jComp '' T) xNew))
      hMember ⟨t, htInT, rfl⟩
  exact ⟨hNotNewComponent, jComp b, hbNew, hNewEdge⟩

end AllThoseRamseyClasses.Lifts
