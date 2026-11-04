import AllThoseRamseyClasses.Lifts.Claim2InnerBoundaryOuterLocalization

/-!
# Claim 2: a weaker geometric invariant for iterating transported closed contexts

The original outer geometric piece P = R ∪ C is function-closed.
After a proper B-only inner flip the transported outer vertex set
K' is known to be function-closed, to preserve its full rooted
forbidden incompatibility profile and ordered root coordinates,
and to have strict B-source descent with conserved exterior A-count.
But it is NOT YET known to be another genuine geometric minimal-cut
piece. Requiring this immediately may be unnecessarily strong.

The minimal source-geometric condition used to locate an inner
B-only S-component is:

  no Gaifman edge may leave K from a vertex of K outside the
  complete shared-root preimage S.

Together with native function-closedness of K, this ensures:
* every S-component starting inside K remains ENTIRELY in K;
* its whole function-generated external boundary lies in S∩K.

This invariant is defined and validated here for arbitrary closed
contexts, not only genuine minimal-separator pieces. Every
geometric outer piece whose root is contained in S satisfies it.

Preservation of this no-escape property under a literal full
functional inner replacement remains an independent next
obligation. Even with that preservation, the final 2019
canonical A→B flip requires a genuinely selected geometric
outer piece or another legitimate selected-piece witness.
These facts are NOT silently assumed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- No native functional Gaifman incidence crosses from inside K
outside the shared-root preimage S to the outside of K.
There is no connectedness or minimal-separator requirement on K. -/
def FunctionalContextNoEscapeOutsideSeam
    (A : Structure L V) (S K : Set V) : Prop :=
  ∀ {x y : V},
    x ∈ K → x ∉ S →
    GaifmanAdjacent A.graph x y → y ∈ K

/-- Every genuine outer geometric piece is automatically
no-escape relative to ANY larger cut S containing its full
ordered root. Its external component boundary is entirely in
the old cut, even for arbitrary native function arities. -/
theorem geometricPiece_noEscapeOutsideContainingSeam
    (A : Structure L V)
    {n : ℕ} (P : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRootInSeam : Set.range P.roots ⊆ S) :
    FunctionalContextNoEscapeOutsideSeam A S
      (geometricPieceVertices A P) := by
  intro x y hx hNotS hEdge
  have hxNotR : x ∉ Set.range P.roots := by
    intro hxR
    exact hNotS (hRootInSeam hxR)
  have hxComp : x ∈ componentFrom A.graph
      (Set.range P.roots) P.left := by
    rcases hx with hxR | hxC
    · exact False.elim (hxNotR hxR)
    · exact hxC
  by_cases hyR : y ∈ Set.range P.roots
  · exact Or.inl hyR
  · exact Or.inr (componentFrom_step
      A.graph (Set.range P.roots) P.left
      hxComp hyR hEdge)

/-- Arbitrary no-escape contexts are saturated by full Gaifman
components after deleting the seam S, independently of their
minimal-separator or rooted profile status. -/
theorem functionalNoEscape_wholeComponent_insideContext
    (A : Structure L V) (S K : Set V)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam A S K)
    (x : {v : V // v ∉ S}) (hxK : x.1 ∈ K) :
    componentFrom A.graph S x ⊆ K := by
  intro z hz
  exact reachOutside_stays_in A.graph S K x hxK
    (by
      intro a b ha hab
      exact hNoEscape ha a.2 hab)
    hz.2

/-- For an arbitrary genuinely function-closed no-escape
context K, the ENTIRE generated external functional boundary
of any S-component starting in K belongs to S∩K.

This is the exact source-localization interface the partner
construction needs at every step of a contextual B-descent.
It does not assume K is a geometric minimal-separator piece. -/
theorem functionalNoEscape_component_generatedBoundary_inside
    (A : Structure L V)
    (S K : Set V)
    (hSclosed : A.IsClosed S)
    (hKclosed : A.IsClosed K)
    (hNoEscape : FunctionalContextNoEscapeOutsideSeam A S K)
    (x : {v : V // v ∉ S}) (hxK : x.1 ∈ K) :
    A.functionClosure
      (gaifmanNeighborhood A.graph (componentFrom A.graph S x))
       ⊆ S ∩ K := by
  have hInside :
      componentFrom A.graph S x ⊆ K :=
    functionalNoEscape_wholeComponent_insideContext
      A S K hNoEscape x hxK
  have hSeed :
      gaifmanNeighborhood A.graph
        (componentFrom A.graph S x) ⊆ K := by
    intro y hy
    obtain ⟨_hyOutside, z, hz, hEdge⟩ := hy
    exact hNoEscape (hInside hz) hz.1 hEdge
  have hKBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph S x)) ⊆ K := by
    intro y hy
    exact hy K hKclosed hSeed
  have hSBoundary :
      A.functionClosure
        (gaifmanNeighborhood A.graph
          (componentFrom A.graph S x)) ⊆ S :=
    functionalClosure_neighborhood_subset_cut A S hSclosed x
  intro y hy
  exact ⟨hSBoundary hy, hKBoundary hy⟩

end AllThoseRamseyClasses.Lifts
