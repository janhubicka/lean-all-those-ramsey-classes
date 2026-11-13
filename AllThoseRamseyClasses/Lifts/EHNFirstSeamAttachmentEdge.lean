import AllThoseRamseyClasses.Lifts.EHNSeamEscapeOrSelectedPiece

/-!
# Track D: first genuine left-exclusive-to-seam Gaifman attachment edge

The verified full native free-amalgam source partition puts every
original source vertex in exactly one of the root-preimage,
left-exclusive or right-exclusive regions. A source Gaifman edge
whose endpoints avoid the root preimage cannot cross between the
left-exclusive and right-exclusive regions.

Given a path in the ACTUAL original source from a chosen
left-exclusive vertex to a right-exclusive vertex avoiding any
S contained in the common-root preimage, the path must pass
through the root-preimage outside S.

We strengthen the prior fresh-seam-vertex theorem: there is an
ACTUAL source Gaifman EDGE a--b such that a is left-exclusive,
b lies in the common root preimage OUTSIDE S, and a can be
reached from the selected left source vertex along a path
avoiding S. This is the first boundary crossing into the
shared-root region on some source path, not an arbitrary distant
seam vertex.

For S equal to the original function-generated input hull,
this is an explicit positive old relation or native function
input/output tuple incident with a truly NEW seam vertex.

This remains an attachment witness, NOT automatically a selected
forbidden geometric piece. We do not assert that the input hull
separates two exterior components, that the new edge realizes an
original ADDED canonical global relation, or that a replacement
strictly reduces original source support.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For an EHN map into a genuine FULL native free amalgam,
every original Gaifman path from a left-exclusive source vertex
to a right-exclusive source vertex avoiding a set S lying
inside the root preimage has a FIRST explicit source attachment
edge from the left-exclusive region into the common seam,
with its seam endpoint outside S.

An actual source path avoiding S reaches the left endpoint of
this edge. The original weak EHN source map need not be
injective, and no forbidden-family hypothesis is required. -/
theorem weakExclusiveGaifmanPath_has_freshLeftSeamAttachmentEdge
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (S : Set V)
    (hSRoot : S ⊆ weakFreeRootPart (sL := sL) (iL := jL) f)
    (x y : V)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := jL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := jL) (iR := jR) f)
    (hPath : ReachOutside Source.graph S
      ⟨x, fun h => hx.2 (hSRoot h)⟩
      ⟨y, fun h => hy.2 (hSRoot h)⟩) :
    ∃ (a b : V) (ha : a ∉ S) (hb : b ∉ S),
      a ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∧
      b ∈ weakFreeRootPart (sL := sL) (iL := jL) f ∧
      GaifmanAdjacent Source.graph a b ∧
      ReachOutside Source.graph S
        ⟨x, fun h => hx.2 (hSRoot h)⟩ ⟨a, ha⟩ := by
  classical
  let xS : {v : V // v ∉ S} :=
    ⟨x, fun h => hx.2 (hSRoot h)⟩
  let yS : {v : V // v ∉ S} :=
    ⟨y, fun h => hy.2 (hSRoot h)⟩
  have hAlong :
      ∀ z : {v : V // v ∉ S},
        ReachOutside Source.graph S xS z →
        (z.1 ∈ weakFreeLeftPart (sL := sL) (iL := jL) f) ∨
        ∃ (a b : {v : V // v ∉ S}),
          a.1 ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∧
          b.1 ∈ weakFreeRootPart (sL := sL) (iL := jL) f ∧
          GaifmanAdjacent Source.graph a.1 b.1 ∧
          ReachOutside Source.graph S xS a := by
    intro z hReach
    induction hReach with
    | refl => exact Or.inl hx
    | @tail a b hab hedge ih =>
        rcases ih with hLeft | ⟨v, w, hvLeft, hwRoot, hVW, hvReach⟩
        · by_cases hbRoot :
              b.1 ∈ weakFreeRootPart (sL := sL) (iL := jL) f
          · exact Or.inr ⟨a, b, hLeft, hbRoot, hedge, hab⟩
          · exact Or.inl
              (weakFreePartition_left_step
                hFree f hf.1 hLeft hbRoot hedge)
        · exact Or.inr ⟨v, w, hvLeft, hwRoot, hVW, hvReach⟩
  rcases hAlong yS hPath with hLeftY |
      ⟨a, b, hLeftA, hRootB, hEdge, hReachA⟩
  · exact False.elim ((Set.disjoint_left.mp
      (weakFreePartition_left_right_disjoint hFree f)) hLeftY hy)
  · exact ⟨a.1, b.1, a.2, b.2,
      hLeftA, hRootB, hEdge, hReachA⟩

/-- In the specific Track D seam-only input hull situation,
a path from an actual original left-exclusive source vertex
to an original right-exclusive source vertex that avoids the
function-closed input hull yields an ACTUAL source Gaifman
attachment EDGE: its first endpoint is left-exclusive, its
second is a NEW common-seam vertex NOT in that closed hull.

The left endpoint itself is reachable along a native Gaifman
path avoiding the hull from the chosen original left source
vertex. No root-injective lift predicate or selected-Q
source replacement is smuggled into this conclusion. -/
theorem ehn_seamInputHull_freshAttachmentEdge_of_nonseparatingPath
    {V UX UA UB UT X : Type}
    (Source : Structure L V)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (xs : X → V)
    (hInputs : ∀ i, f (xs i) ∈ Set.range (jL.comp sL))
    (x y : V)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := jL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := jL) (iR := jR) f)
    (hPath : ReachOutside Source.graph
      (Source.functionClosure (Set.range xs))
      ⟨x, fun h => hx.2
        (ehn_seamInputs_generatedClosedHull_insideRootPreimage
          Source Root Left Right Target sL sR jL jR
          f hf xs hInputs h)⟩
      ⟨y, fun h => hy.2
        (ehn_seamInputs_generatedClosedHull_insideRootPreimage
          Source Root Left Right Target sL sR jL jR
          f hf xs hInputs h)⟩) :
    ∃ (a b : V) (ha : a ∉ Source.functionClosure (Set.range xs))
        (hb : b ∉ Source.functionClosure (Set.range xs)),
      a ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∧
      b ∈ weakFreeRootPart (sL := sL) (iL := jL) f ∧
      GaifmanAdjacent Source.graph a b ∧
      ReachOutside Source.graph
        (Source.functionClosure (Set.range xs))
        ⟨x, fun h => hx.2
          (ehn_seamInputs_generatedClosedHull_insideRootPreimage
            Source Root Left Right Target sL sR jL jR
            f hf xs hInputs h)⟩ ⟨a, ha⟩ := by
  have hRoot :
      Source.functionClosure (Set.range xs) ⊆
        weakFreeRootPart (sL := sL) (iL := jL) f :=
    ehn_seamInputs_generatedClosedHull_insideRootPreimage
      Source Root Left Right Target sL sR jL jR f hf xs hInputs
  exact weakExclusiveGaifmanPath_has_freshLeftSeamAttachmentEdge
    Source Root Left Right Target
    sL sR jL jR hFree f hf
    (Source.functionClosure (Set.range xs)) hRoot
    x y hx hy hPath

end AllThoseRamseyClasses.Lifts
