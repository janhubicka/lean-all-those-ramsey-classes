import AllThoseRamseyClasses.Lifts.EHNTwoExteriorComponentsSelectedPiece

/-!
# Track D: any newly selected minimal closed separator must hit new growth

Let S be an earlier source vertex set which does NOT separate a
chosen pair of exterior vertices. Let T be a later NATIVE FUNCTION-
CLOSED source set which DOES separate them. The previously checked
finite closed-separator selector chooses a genuine inclusion-minimal
closed cut C ⊆ T for this same pair.

Then C cannot be contained in S: if it were, the original Gaifman
path avoiding S would also avoid C, contradicting C's defining
separation property. Thus at least one actual ordered source root of
the selected geometric piece lies in T \ S.

This is the precise RETENTION fact available from the last step of
a seam-saturation proof. It is weaker than saying the newly adjoined
generator itself belongs to C: arbitrary native function closure
may add further vertices and the selected cut can include one of
those instead. In particular C need not contain the original
positive-incidence-defective input hull.

No source-image quotient, root-image injectivity, family
image-closure shortcut, canonical profile or flip is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If the actual original source has a Gaifman path between
the two selected exterior vertices avoiding S, and the genuine
geometric minimal closed separator C between them has both
vertices outside S, then at least one of the distinct ordered
original source roots of C is not in S.

The proof uses monotonicity of TRUE Gaifman paths under shrinking
the deleted cut, and no finiteness or function closure premise. -/
theorem geometricMinimalClosedSeparator_rootEscapes_nonSeparatingEarlierSet
    {V : Type}
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hxS : d.left.1 ∉ S)
    (hyS : d.right.1 ∉ S)
    (hPath : ReachOutside A.graph S
      ⟨d.left.1, hxS⟩ ⟨d.right.1, hyS⟩) :
    ∃ i : Fin n, d.roots i ∉ S := by
  classical
  by_contra hNo
  have hRootsInS : Set.range d.roots ⊆ S := by
    rintro v ⟨i, rfl⟩
    by_contra hi
    exact hNo ⟨i, hi⟩
  have hReach :
      ReachOutside A.graph (Set.range d.roots)
        (outsideCutMap hRootsInS ⟨d.left.1, hxS⟩)
        (outsideCutMap hRootsInS ⟨d.right.1, hyS⟩) :=
    reachOutside_of_cut_subset A.graph hRootsInS
      ⟨d.left.1, hxS⟩ ⟨d.right.1, hyS⟩ hPath
  exact d.minimal.2.1 (by
    simpa only [outsideCutMap] using hReach)

/-- Strengthen the ACTUAL native finite minimal-closed-separator
selection: if a true earlier S ⊆ T does NOT separate the chosen
original exterior vertices and the later CLOSED T DOES separate
them, the selected positive-width geometric piece has at least
one genuine ordered original SOURCE root in T \ S.

This preserves the actual two source endpoints, the complete
native function-closed root and positive root width. It does NOT
assert that the entire earlier set or its original defective
input tuple is retained by the selected cut. -/
theorem finiteSelectedGeometricPiece_rootHits_newClosedHullGrowth
    {V : Type}
    [Finite V]
    (A : Structure L V)
    (S T : Set V)
    (hST : S ⊆ T)
    (hTClosed : A.IsClosed T)
    (x y : {v : V // v ∉ T})
    (hPathS : ReachOutside A.graph S
      (outsideCutMap hST x) (outsideCutMap hST y))
    (hSeparatedT : ¬ ReachOutside A.graph T x y)
    (hConnected :
      Relation.ReflTransGen (GaifmanAdjacent A.graph) x.1 y.1) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData A n),
      0 < n ∧
      Set.range d.roots ⊆ T ∧
      d.left.1 = x.1 ∧
      d.right.1 = y.1 ∧
      ∃ i : Fin n, d.roots i ∉ S := by
  obtain ⟨n, d, hn, hRoot, hLeft, hRight⟩ :=
    finiteClosedCut_twoExteriorComponents_selectPositivePiece
      A T hTClosed x y hSeparatedT hConnected
  have hxS : d.left.1 ∉ S := by
    rw [hLeft]
    exact fun h => x.2 (hST h)
  have hyS : d.right.1 ∉ S := by
    rw [hRight]
    exact fun h => y.2 (hST h)
  have hPathD : ReachOutside A.graph S
      ⟨d.left.1, hxS⟩ ⟨d.right.1, hyS⟩ := by
    simpa only [hLeft, hRight, outsideCutMap] using hPathS
  obtain ⟨i, hi⟩ :=
    geometricMinimalClosedSeparator_rootEscapes_nonSeparatingEarlierSet
      A d S hxS hyS hPathD
  exact ⟨n, d, hn, hRoot, hLeft, hRight, i, hi⟩

end AllThoseRamseyClasses.Lifts
