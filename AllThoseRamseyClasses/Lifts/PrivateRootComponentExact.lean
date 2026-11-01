import AllThoseRamseyClasses.Lifts.FullFreeAmalgamNewOuterConfinement

/-!
# Exact private components outside the FULL inner root in a native free amalgam

An ACTUAL full native functional free amalgam
  Whole = Left +_Root Right
does not connect private vertices of different sides by an edge
after removing the COMPLETE shared root. The verified tuple-side
locality lemma excludes all relation/function incidence tuples
crossing the two private parts, including arbitrary-arity inputs
and outputs of set-valued partial functions.

This module strengthens exterior-component preservation: for a
component after deleting exactly the FULL gluing root, the
whole-source component is the image of the original right-side
component WITHOUT presupposing an equation for its generated
neighbourhood boundary. Consequently the theorem can be used
to ESTABLISH (not assume) that selected geometric source pieces
have the full generated root internally, by reflecting their
already verified whole-source boundary.

No target weak EHN map or forbidden-family hypothesis is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every component outside the COMPLETE common root on the
right side is exactly the image of one right-side component.
No private vertex can escape through higher-arity Gaifman edges.
In contrast to the earlier exterior-component theorem, no
generated-boundary equality is required. -/
theorem fullFreeAmalgam_rightPrivateRoot_component_eq
    {H E B W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (x : {b : B // b ∉ Set.range sR}) :
    componentFrom Whole.graph (iR '' Set.range sR)
      (fullFunctionalEmbedding_outsideCut iR
        (Set.range sR) x) =
    iR '' componentFrom Right.graph (Set.range sR) x := by
  let U : Set W := iR '' Set.range sR
  let root : {w : W // w ∉ U} :=
    fullFunctionalEmbedding_outsideCut iR (Set.range sR) x
  have hTransport :
      ∀ y : {w : W // w ∉ U},
        ReachOutside Whole.graph U root y →
          ∃ b : {z : B // z ∉ Set.range sR},
            iR b.1 = y.1 ∧
              ReachOutside Right.graph (Set.range sR) x b := by
    intro y hReach
    induction hReach with
    | refl =>
        exact ⟨x, rfl, Relation.ReflTransGen.refl⟩
    | @tail a b hpre hedge ih =>
        obtain ⟨aR, haMap, haPath⟩ := ih
        have haPrivate : aR.1 ∉ Set.range sR := aR.2
        have hWholeEdge :
            GaifmanAdjacent Whole.graph (iR aR.1) b.1 := by
          rw [haMap]
          exact hedge
        obtain ⟨bR, hbMap⟩ :=
          fullFreeAmalgam_rightPrivate_neighbor_in_right
            hFree aR.1 haPrivate b.1 hWholeEdge
        have hbPrivate : bR ∉ Set.range sR := by
          intro hbRoot
          exact b.2 ⟨bR, hbRoot, hbMap⟩
        let b' : {z : B // z ∉ Set.range sR} :=
          ⟨bR, hbPrivate⟩
        have hRightEdge : GaifmanAdjacent Right.graph aR.1 bR :=
          (fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
            hFree aR.1 bR haPrivate).mp (by
              rw [haMap, hbMap]
              exact hedge)
        exact ⟨b', hbMap, haPath.tail hRightEdge⟩
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨b, hbEq, hbPath⟩ :=
      hTransport ⟨z, hz.1⟩ hz.2
    exact ⟨b.1, ⟨b.2, hbPath⟩, hbEq⟩
  · rintro z ⟨b, hb, rfl⟩
    have hPath :
        ReachOutside Whole.graph U root
          (fullFunctionalEmbedding_outsideCut iR
            (Set.range sR) ⟨b, hb.1⟩) :=
      fullFunctionalEmbedding_reachOutside_map iR
        (Set.range sR) hb.2
    exact ⟨(fullFunctionalEmbedding_outsideCut iR
      (Set.range sR) ⟨b, hb.1⟩).2, hPath⟩

end AllThoseRamseyClasses.Lifts
