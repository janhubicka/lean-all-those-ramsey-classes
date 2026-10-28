import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGaifman

/-!
# Exact external neighbourhood of the unchanged private functional side

An actual full native free amalgam has no relation/function incidence
crossing its exclusive sides. If C is ANY set of right-private
vertices (outside an SR containing the common full root), the
EXTERNAL GAIFMAN NEIGHBOURHOOD of its embedded image in the whole
source is exactly the image of its original right-side neighbourhood.

The forward direction is stronger than the ordinary induced-embedding
property: a whole-source tuple containing a private right vertex
must come ENTIRELY from Right. It can therefore neither introduce
new Gaifman neighbours from the left-private side nor lose right
incidences. Every output and input coordinate of an original
set-valued partial function is included in the graph argument.

This is the missing graphical ingredient for transporting the
entire GENERATED boundary of a component under a contextual B-only
flip, once the separate exact functional-closure-image theorem is
merged. The source context's outer minimal-separator property
and all-test incompatibility profile remain separate obligations.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L W}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The WHOLE-SOURCE Gaifman neighbourhood of the embedding of
any right-private subset is literally the embedding of its
right-side neighbourhood. There are NO extra neighbours in Left.

Only source-full-amalgam geometry is used. The forbidden weak map,
its fibre images, and the particular nested old piece play no role. -/
theorem fullFreeAmalgam_rightPrivate_neighborhood_eq_image
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR C : Set F)
    (hRootR : ∀ r : H, sR r ∈ SR)
    (hCPrivate : C ⊆ {b : F | b ∉ SR}) :
    gaifmanNeighborhood Whole.graph (iR '' C) =
      iR '' gaifmanNeighborhood Right.graph C := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨hzNotC, cImage, hcImage, hEdge⟩ := hz
    obtain ⟨c, hcC, hcMap⟩ := hcImage
    have hcPrivate : c ∉ Set.range sR := by
      rintro ⟨r, hr⟩
      exact (hCPrivate hcC) (hr ▸ hRootR r)
    have hEdge' : GaifmanAdjacent Whole.graph (iR c) z := by
      rw [hcMap]
      exact hEdge
    obtain ⟨hne, sym, xs, j, k, htuple, hj, hk⟩ := hEdge'
    rcases functionalFreeAmalgam_graphTuple_side
        hFree sym xs htuple with hLeft | hRight
    · obtain ⟨a, ha⟩ := hLeft j
      have hOverlap : iL a = iR c := ha.symm.trans hj
      obtain ⟨r, _, hcRoot⟩ := (hFree.overlap a c).mp hOverlap
      exact False.elim (hcPrivate ⟨r, hcRoot.symm⟩)
    · obtain ⟨b, hb⟩ := hRight k
      have hzMap : z = iR b := hk.symm.trans hb
      have hWholeEdge :
          GaifmanAdjacent Whole.graph (iR c) (iR b) := by
        refine ⟨?_, sym, xs, j, k, htuple, hj, hk.trans hzMap⟩
        intro hEq
        exact hne (hEq.trans hzMap.symm)
      have hRightEdge : GaifmanAdjacent Right.graph c b :=
        (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
          hFree c b hcPrivate).mp hWholeEdge
      have hbNotC : b ∉ C := by
        intro hbC
        exact hzNotC ⟨b, hbC, hzMap.symm⟩
      exact ⟨b, ⟨hbNotC, c, hcC, hRightEdge⟩,
        hzMap.symm⟩
  · rintro z ⟨b, hbN, rfl⟩
    obtain ⟨hbNotC, c, hcC, hRightEdge⟩ := hbN
    have hcPrivate : c ∉ Set.range sR := by
      rintro ⟨r, hr⟩
      exact (hCPrivate hcC) (hr ▸ hRootR r)
    have hWholeEdge : GaifmanAdjacent Whole.graph (iR c) (iR b) :=
      (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
        hFree c b hcPrivate).mpr hRightEdge
    refine ⟨?_, iR c, ⟨c, hcC, rfl⟩, hWholeEdge⟩
    rintro ⟨d, hdC, hdMap⟩
    have hdb : d = b := iR.injective hdMap
    exact hbNotC (hdb ▸ hdC)

end AllThoseRamseyClasses.Lifts
