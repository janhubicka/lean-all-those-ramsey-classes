import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# Restricting a closed source cut to a genuine geometric piece

Let (P,R) be a genuine finite or infinite geometric functional
piece of A, with P = R ∪ C where C is a Gaifman component of A \ R.
Let S be ANY vertex cut containing R. Set T = S ∩ P.

For every vertex x ∈ C \ S, its Gaifman component after deleting
T is EXACTLY its component after deleting S. Indeed, a path from
x avoiding T cannot leave C: every external neighbour of C lies
in R ⊆ T. Once the path stays inside C ⊆ P, avoiding T is the same
as avoiding S. This argument needs no global source connectivity,
no finite carrier and no homomorphism-image injectivity.

When S is function-closed, so is T, since P is a real closed
functional substructure. Thus any closed separator in S of two
vertices in the original component can be localized to P, while
preserving its two actual source Gaifman components.

This is the missing localization needed before constructing a
PROPER sub-piece in Section 3 Claim 2. It does NOT establish the
still-open two-boundary-closure hypothesis for the specific
opposite-side components chosen in the published argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A source's genuine geometric piece is closed under its native
functions, including nullary function incidences. Intersecting it
with another function-closed set is again closed. -/
theorem geometricPiece_intersectClosedCut_isClosed
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V) (hS : A.IsClosed S) :
    A.IsClosed (S ∩ geometricPieceVertices A d) := by
  have hP : A.IsClosed (geometricPieceVertices A d) :=
    functionalComponentUnion_isClosed
      A (Set.range d.roots) d.minimal.1 d.left
  intro f xs hxs y hy
  exact ⟨hS f xs (fun i => (hxs i).1) hy,
    hP f xs (fun i => (hxs i).2) hy⟩

/-- The original root is still contained in the intersection
of the larger cut with the whole piece. -/
theorem geometricPiece_root_subset_intersectCut
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V) (hRS : Set.range d.roots ⊆ S) :
    Set.range d.roots ⊆ S ∩ geometricPieceVertices A d := by
  intro z hz
  exact ⟨hRS hz, Or.inl hz⟩

/-- If S contains the original geometric root R, every vertex
x of the selected component C outside S has exactly the same
source Gaifman component in A \ S and in A \ (S ∩ P).

This is equality of WHOLE component sets, not just reachability of
the two selected roots. No closedness assumption on S is necessary
for the graph-theoretic equality. -/
theorem geometricPiece_component_intersectCut_eq
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRS : Set.range d.roots ⊆ S)
    (x : {v : V // v ∉ S})
    (hxC : x.1 ∈ functionalComponentFrom
      A (Set.range d.roots) d.left) :
    componentFrom A.graph (S ∩ geometricPieceVertices A d)
      (outsideCutMap (Set.inter_subset_left) x) =
    componentFrom A.graph S x := by
  let R : Set V := Set.range d.roots
  let C : Set V := functionalComponentFrom A R d.left
  let P : Set V := geometricPieceVertices A d
  let T : Set V := S ∩ P
  have hTS : T ⊆ S := Set.inter_subset_left
  let xT : {v : V // v ∉ T} := outsideCutMap hTS x
  have hBoundary : gaifmanNeighborhood A.graph C ⊆ T := by
    intro z hz
    have hzR : z ∈ R :=
      gaifmanNeighborhood_component_subset_cut A.graph R d.left hz
    exact ⟨hRS hzR, Or.inl hzR⟩
  have hAvoidS (t : {v : V // v ∉ T}) (htC : t.1 ∈ C) :
      t.1 ∉ S := by
    intro htS
    exact t.2 ⟨htS, Or.inr htC⟩
  have hLift :
      ∀ (t : {v : V // v ∉ T}),
        ReachOutside A.graph T xT t →
        ∃ (htC : t.1 ∈ C),
          ReachOutside A.graph S x
            ⟨t.1, hAvoidS t htC⟩ := by
    intro t hPath
    induction hPath with
    | refl =>
        exact ⟨hxC, Relation.ReflTransGen.refl⟩
    | @tail a b hab hedge ih =>
        obtain ⟨haC, haReach⟩ := ih
        have hbNotR : b.1 ∉ R := by
          intro hbR
          exact b.2 ⟨hRS hbR, Or.inl hbR⟩
        have hbC : b.1 ∈ C :=
          componentFrom_step A.graph R d.left haC hbNotR hedge
        have hStepS : outsideAdjacency A.graph S
            ⟨a.1, hAvoidS a haC⟩
            ⟨b.1, hAvoidS b hbC⟩ := hedge
        exact ⟨hbC, haReach.tail hStepS⟩
  apply Set.Subset.antisymm
  · intro z hzT
    obtain ⟨hzNotT, hzPathT⟩ := hzT
    obtain ⟨hzC, hzPathS⟩ :=
      hLift ⟨z, hzNotT⟩ hzPathT
    exact ⟨hAvoidS ⟨z, hzNotT⟩ hzC, hzPathS⟩
  · exact componentFrom_subset_of_cut_subset A.graph hTS x

/-- A closed S separating two vertices of the selected old piece
continues to separate them after restricting its cut to S ∩ P.
The proof uses exact component equality, not the false assertion
that an arbitrary outside-P path can simply be discarded. -/
theorem geometricPiece_intersectCut_separates
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (S : Set V)
    (hRS : Set.range d.roots ⊆ S)
    (x y : {v : V // v ∉ S})
    (hxC : x.1 ∈ functionalComponentFrom
      A (Set.range d.roots) d.left)
    (hSepS : ¬ ReachOutside A.graph S x y) :
    ¬ ReachOutside A.graph (S ∩ geometricPieceVertices A d)
      (outsideCutMap Set.inter_subset_left x)
      (outsideCutMap Set.inter_subset_left y) := by
  intro hPath
  have hyT :
      y.1 ∈ componentFrom A.graph
        (S ∩ geometricPieceVertices A d)
        (outsideCutMap Set.inter_subset_left x) :=
    ⟨(outsideCutMap Set.inter_subset_left y).2, hPath⟩
  have hyS : y.1 ∈ componentFrom A.graph S x := by
    rw [geometricPiece_component_intersectCut_eq A d S hRS x hxC] at hyT
    exact hyT
  exact hSepS hyS.2

end AllThoseRamseyClasses.Lifts
