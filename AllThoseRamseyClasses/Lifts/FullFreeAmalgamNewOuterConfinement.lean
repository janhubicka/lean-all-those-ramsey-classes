import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGaifman
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamExteriorOldRoot

/-!
# No escape of new outer-cut paths into an unrelated retained component

Suppose New = NewInner +_U Complement is a genuine FULL native
functional free amalgam. The entire complete Complement also embeds
fully in an old source Old. Let T be any subset of Complement, not
necessarily comparable with U. Fix an actual component C of Old
after deleting the embedded T.

If every surviving common root vertex U\\T already belongs to C in
Old, then any New\\T path starting in the NewInner image and ending
in the Complement image can only end at a vertex whose OLD image
belongs to C, unless its endpoint still belongs to NewInner.

This is the reverse-component containment mechanism in Track A:
a freshly inserted component cannot create an outside-T route to
an unrelated old exterior component. The proof is entirely in
the full SOURCE structures, with arbitrary old partial functions
and their complete incidence tuples. No weak EHN map is involved.

An essential edge fact is that any New Gaifman neighbour of a
right-private vertex remains in the complete right-hand side.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A private Complement vertex of a FULL native free amalgam has
no whole-source Gaifman neighbour outside the Complement image.
This includes incidence edges of arbitrary-arity partial functions. -/
theorem fullFreeAmalgam_rightPrivate_neighbor_in_right
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
    (b : B) (hbPrivate : b ∉ Set.range sComp)
    (w : W)
    (hEdge : GaifmanAdjacent Whole.graph (iComp b) w) :
    w ∈ Set.range iComp := by
  rcases hEdge with ⟨_, sym, xs, j, k, htuple, hj, hk⟩
  rcases functionalFreeAmalgam_graphTuple_side
      hFree sym xs htuple with hLeft | hRight
  · obtain ⟨e, he⟩ := hLeft j
    have heq : iInner e = iComp b := he.symm.trans hj
    obtain ⟨r, _, hr⟩ := (hFree.overlap e b).mp heq
    exact False.elim (hbPrivate ⟨r, hr.symm⟩)
  · obtain ⟨c, hc⟩ := hRight k
    exact ⟨c, hc.symm.trans hk⟩

/-- Let C be a genuine old source component after deleting the full
image of T. Assume all surviving inner-root vertices already lie in C.
A New source path starting in the inserted inner-side image cannot
reach an OLD-complement vertex outside C, except while its endpoint
remains part of the New inner-side image itself.

The conclusion is a disjunction because a common-root vertex has
both left and right representations. After restricting to right-private
vertices, the first alternative is impossible by free-amalgam overlap.

No assumptions about root-order nesting or forbidden-source
injectivization appear. -/
theorem fullFreeAmalgam_newOuterComponent_confined_to_old
    {H E B W W' : Type v}
    {Root : Structure L H}
    {NewInner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding Root NewInner}
    {sComp : Structure.Embedding Root Complement}
    {jInner : Structure.Embedding NewInner New}
    {jComp : Structure.Embedding Complement New}
    (hFree : Structure.IsFreeAmalgam sInner sComp jInner jComp)
    (iComp : Structure.Embedding Complement Old)
    (T : Set B)
    (xOld : {w : W // w ∉ iComp '' T})
    (hRootOld :
      ∀ r : H, sComp r ∉ T →
        iComp (sComp r) ∈
          componentFrom Old.graph (iComp '' T) xOld)
    (xNew : {w : W' // w ∉ jComp '' T})
    (hxNew : xNew.1 ∈ Set.range jInner)
    (yNew : {w : W' // w ∉ jComp '' T})
    (hReach : ReachOutside New.graph (jComp '' T) xNew yNew) :
    yNew.1 ∈ Set.range jInner ∨
      ∃ b : B, jComp b = yNew.1 ∧
        iComp b ∈ componentFrom Old.graph (iComp '' T) xOld := by
  let C : Set W := componentFrom Old.graph (iComp '' T) xOld
  have hStay : ∀ z : {w : W' // w ∉ jComp '' T},
      ReachOutside New.graph (jComp '' T) xNew z →
      (z.1 ∈ Set.range jInner ∨
        ∃ b : B, jComp b = z.1 ∧ iComp b ∈ C) := by
    intro z hPath
    induction hPath with
    | refl =>
        exact Or.inl hxNew
    | @tail a b hpre hedge ih =>
        rcases hFree.covers b.1 with ⟨e, he⟩ | ⟨bR, hbMap⟩
        · exact Or.inl ⟨e, he.symm⟩
        · have hbNotT : bR ∉ T := by
            intro hbT
            exact b.2 ⟨bR, hbT, hbMap.symm⟩
          by_cases hbRoot : bR ∈ Set.range sComp
          · obtain ⟨r, hr⟩ := hbRoot
            have hrNotT : sComp r ∉ T := by
              intro hrT
              exact hbNotT (hr ▸ hrT)
            have hOld : iComp bR ∈ C := by
              rw [← hr]
              exact hRootOld r hrNotT
            exact Or.inr ⟨bR, hbMap.symm, hOld⟩
          · have hReverse :
                GaifmanAdjacent New.graph (jComp bR) a.1 := by
              rw [← hbMap]
              exact GaifmanAdjacent.symm hedge
            obtain ⟨aR, haMap⟩ :=
              fullFreeAmalgam_rightPrivate_neighbor_in_right
                hFree bR hbRoot a.1 hReverse
            have haNotT : aR ∉ T := by
              intro haT
              exact a.2 ⟨aR, haT, haMap⟩
            have haOld : iComp aR ∈ C := by
              rcases ih with ⟨aL, haLeft⟩ | ⟨aR', haRight, haC⟩
              · obtain ⟨r, _, hr⟩ :=
                  (hFree.overlap aL aR).mp (haLeft.trans haMap.symm)
                have hrNotT : sComp r ∉ T := by
                  intro hrT
                  exact haNotT (hr ▸ hrT)
                rw [hr]
                exact hRootOld r hrNotT
              · have hEqual : aR' = aR :=
                  jComp.injective (haRight.trans haMap.symm)
                simpa only [hEqual] using haC
            have hNewEdge :
                GaifmanAdjacent New.graph (jComp bR) (jComp aR) := by
              rw [← hbMap, haMap]
              exact GaifmanAdjacent.symm hedge
            have hRightEdge : GaifmanAdjacent Complement.graph aR bR :=
              GaifmanAdjacent.symm
                ((fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
                  hFree bR aR hbRoot).mp hNewEdge)
            have hOldEdge :
                GaifmanAdjacent Old.graph (iComp aR) (iComp bR) :=
              fullFunctionalEmbedding_gaifmanEdge_map iComp hRightEdge
            have hbOldNotCut : iComp bR ∉ iComp '' T := by
              rintro ⟨c, hc, hcb⟩
              have heq : c = bR := iComp.injective hcb
              exact hbNotT (heq ▸ hc)
            have hOldB : iComp bR ∈ C :=
              componentFrom_step Old.graph (iComp '' T)
                xOld haOld hbOldNotCut hOldEdge
            exact Or.inr ⟨bR, hbMap.symm, hOldB⟩
  exact hStay yNew hReach

/-- A right-PRIVATE endpoint of the new outer-cut component really
comes from the old outer component, not merely from the new inner
piece. This is the exact no-escape statement needed in Claim 2. -/
theorem fullFreeAmalgam_newOuterRightPrivate_inside_oldComponent
    {H E B W W' : Type v}
    {Root : Structure L H}
    {NewInner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding Root NewInner}
    {sComp : Structure.Embedding Root Complement}
    {jInner : Structure.Embedding NewInner New}
    {jComp : Structure.Embedding Complement New}
    (hFree : Structure.IsFreeAmalgam sInner sComp jInner jComp)
    (iComp : Structure.Embedding Complement Old)
    (T : Set B)
    (xOld : {w : W // w ∉ iComp '' T})
    (hRootOld :
      ∀ r : H, sComp r ∉ T →
        iComp (sComp r) ∈
          componentFrom Old.graph (iComp '' T) xOld)
    (xNew : {w : W' // w ∉ jComp '' T})
    (hxNew : xNew.1 ∈ Set.range jInner)
    (b : B) (hbPrivate : b ∉ Set.range sComp)
    (hbNotT : b ∉ T)
    (hReach : ReachOutside New.graph (jComp '' T) xNew
      (fullFunctionalEmbedding_outsideCut jComp T ⟨b, hbNotT⟩)) :
    iComp b ∈ componentFrom Old.graph (iComp '' T) xOld := by
  rcases fullFreeAmalgam_newOuterComponent_confined_to_old
      hFree iComp T xOld hRootOld xNew hxNew
      (fullFunctionalEmbedding_outsideCut jComp T ⟨b, hbNotT⟩)
      hReach with hInLeft | ⟨b', hbMap, hOld⟩
  · obtain ⟨e, he⟩ := hInLeft
    obtain ⟨r, _, hr⟩ :=
      (hFree.overlap e b).mp (he.trans (by rfl))
    exact False.elim (hbPrivate ⟨r, hr.symm⟩)
  · have hEq : b' = b := jComp.injective hbMap
    simpa only [hEq] using hOld

end AllThoseRamseyClasses.Lifts
