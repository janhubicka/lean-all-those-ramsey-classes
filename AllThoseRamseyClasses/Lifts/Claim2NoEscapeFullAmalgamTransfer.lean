import AllThoseRamseyClasses.Lifts.Claim2ClosedContextNoEscape
import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateOuterComponentIff

/-!
# Claim 2: the no-escape invariant survives a genuine native inner replacement

Consider TWO genuine full functional free-amalgam diagrams
  Old = OldInner +_U Complement
  New = NewInner +_U Complement
over the SAME full native complement structure and ordered root.

Let SR be any subset of the retained complement. Write the
corresponding contextual carriers:
  KOld = image(OldInner) ∪ image(SR) in Old,
  KNew = image(NewInner) ∪ image(SR) in New.

Let SOld and SNew be arbitrary cuts (in Claim 2, preimages of
the common target amalgam root). Assume all common gluing-root
vertices lie in SNew and the two cuts agree coordinatewise
on the retained complement. Then:

  NoEscape(Old, SOld, KOld) implies
  NoEscape(New, SNew, KNew).

The proof is an EXACT native Gaifman-incidence argument.
A private inner vertex can only have neighbours on its new
inner side, which is wholly included in KNew. A private right
vertex with a neighbour in the right complement has the SAME
incidence in both old and new whole sources: the full native
free-amalgam right-private adjacency equivalence reflects
the entire original functional graph tuple. If an old right
neighbour belongs to KOld only through the old inner side,
the true overlap theorem identifies it with a shared ROOT,
which likewise belongs to KNew's inserted inner side.

This theorem needs no new-outer-minimal-separator geometry,
no weak target-map injectivity, no A-support minimality,
and no assumption that SR contains the common root.

It is the missing stability interface for an alternative
Claim 2 iteration based on closed, no-escape outer contexts.
The terminal genuine-selected-piece issue remains separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Two genuine full native functional free amalgams sharing
the entire complementary side preserve the "no source
Gaifman edge escapes from K outside the shared target seam"
property across arbitrary replacement of the inner side.

The common-root image belongs to the new seam; the old and
new seam predicates agree on ALL retained right vertices.
Neither is a premise about the new minimal-cut geometry. -/
theorem fullFreeAmalgam_noEscape_preserved_under_innerReplacement
    {H OL NL E V W : Type v}
    {Root : Structure L H}
    {OldInner : Structure L OL}
    {NewInner : Structure L NL}
    {Complement : Structure L E}
    {Old : Structure L V}
    {New : Structure L W}
    {sOldL : Structure.Embedding Root OldInner}
    {sNewL : Structure.Embedding Root NewInner}
    {sR : Structure.Embedding Root Complement}
    {iOldL : Structure.Embedding OldInner Old}
    {iOldR : Structure.Embedding Complement Old}
    {iNewL : Structure.Embedding NewInner New}
    {iNewR : Structure.Embedding Complement New}
    (hOldFree : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNewFree : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (SOld : Set V) (SNew : Set W) (SR : Set E)
    (hNewRootInSeam : ∀ r : H, iNewR (sR r) ∈ SNew)
    (hSeamAgreement : ∀ b : E,
      iNewR b ∈ SNew ↔ iOldR b ∈ SOld)
    (hOldNoEscape :
      FunctionalContextNoEscapeOutsideSeam Old SOld
        (iOldL '' (Set.univ : Set OL) ∪ iOldR '' SR)) :
    FunctionalContextNoEscapeOutsideSeam New SNew
      (iNewL '' (Set.univ : Set NL) ∪ iNewR '' SR) := by
  intro x y hxK hxNotS hEdge
  rcases hxK with hxL | hxR
  · obtain ⟨a, _ha, rfl⟩ := hxL
    have haPrivate : a ∉ Set.range sNewL := by
      rintro ⟨r, rfl⟩
      have hRootOverlap :
          iNewL (sNewL r) = iNewR (sR r) :=
        (hNewFree.overlap (sNewL r) (sR r)).mpr
          ⟨r, rfl, rfl⟩
      apply hxNotS
      rw [hRootOverlap]
      exact hNewRootInSeam r
    obtain ⟨a', ha'⟩ :=
      fullFreeAmalgam_leftPrivate_neighbor_in_left
        hNewFree a haPrivate y hEdge
    exact Or.inl ⟨a', Set.mem_univ _, ha'⟩
  · obtain ⟨b, hbSR, rfl⟩ := hxR
    have hbPrivate : b ∉ Set.range sR := by
      rintro ⟨r, rfl⟩
      exact hxNotS (hNewRootInSeam r)
    obtain ⟨b', hb'⟩ :=
      fullFreeAmalgam_rightPrivate_neighbor_in_right
        hNewFree b hbPrivate y hEdge
    subst y
    have hCompEdge : GaifmanAdjacent Complement.graph b b' :=
      (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
        hNewFree b b' hbPrivate).mp hEdge
    have hOldEdge :
        GaifmanAdjacent Old.graph (iOldR b) (iOldR b') :=
      (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
        hOldFree b b' hbPrivate).mpr hCompEdge
    have hOldK :
        iOldR b ∈ iOldL '' (Set.univ : Set OL) ∪ iOldR '' SR :=
      Or.inr ⟨b, hbSR, rfl⟩
    have hbNotOldS : iOldR b ∉ SOld := by
      intro hbOldS
      exact hxNotS ((hSeamAgreement b).mpr hbOldS)
    have hOldY :
        iOldR b' ∈
          iOldL '' (Set.univ : Set OL) ∪ iOldR '' SR :=
      hOldNoEscape hOldK hbNotOldS hOldEdge
    rcases hOldY with hyOldL | hyOldR
    · obtain ⟨a, _ha, haEq⟩ := hyOldL
      obtain ⟨r, _hrL, hrR⟩ :=
        (hOldFree.overlap a b').mp haEq
      have hRootOverlap :
          iNewL (sNewL r) = iNewR (sR r) :=
        (hNewFree.overlap (sNewL r) (sR r)).mpr
          ⟨r, rfl, rfl⟩
      refine Or.inl ⟨sNewL r, Set.mem_univ _, ?_⟩
      exact hRootOverlap.trans (congrArg iNewR hrR.symm)
    · obtain ⟨b'', hb''SR, hb''Eq⟩ := hyOldR
      have hbEq : b'' = b' := iOldR.injective hb''Eq
      have hb'SR : b' ∈ SR := by
        simpa only [hbEq] using hb''SR
      exact Or.inr ⟨b', hb'SR, rfl⟩

end AllThoseRamseyClasses.Lifts
