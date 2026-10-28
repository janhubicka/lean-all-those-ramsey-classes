import AllThoseRamseyClasses.Lifts.FullFreeAmalgamPrivateGeneratedBoundary
import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# The exterior component of an outer piece survives an inner source flip

Let Whole = Left +_Root Right be a genuine FULL native functional
free amalgam and T ANY closed or nonclosed right-side vertex cut.
The cut T is NOT required to contain the inner amalgamation root!

Suppose C is a complete component of Right minus T, entirely
disjoint from the full common gluing-root range, and its COMPLETE
generated external neighbourhood boundary satisfies Cl_R(N_R(C))=T.

All positive relation/function incidences touching the private
component C belong to Right, so the verified exact functional
boundary transport gives Cl_Whole(N_Whole(iRight(C)))=iRight(T).
In particular every WHOLE-source neighbour of iRight(C)
outside iRight(C) lies in iRight(T).

An actual Gaifman path in Right\T maps forward along the FULL
source embedding iRight. Conversely a path in Whole\iRight(T)
starting in iRight(C) CANNOT LEAVE it, since it would cross the
entire preserved boundary iRight(T). Therefore iRight(C) is
EXACTLY a component of Whole minus the transported old root.

This establishes preservation of the EXTERIOR component and
its complete generated boundary through the native inner
replacement even when the old outer root does not contain the
inner gluing seam. This is stronger than the previously checked
outside-CONTEXT component equality, and directly addresses one
half of the 2019 Claim 2 outer minimal-separator geometry.

It does NOT prove an opposite INNER component with the same
complete root boundary, nor outer piece connectedness or
all-test incompatibility-profile congruence.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A FULL native functional embedding preserves every genuine
source Gaifman edge, including edges from complete function
incidence tuples. The map need not be surjective. -/
theorem fullFunctionalEmbedding_gaifmanEdge_map
    {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B)
    {x y : V}
    (h : GaifmanAdjacent A.graph x y) :
    GaifmanAdjacent B.graph (e x) (e y) := by
  rcases h with ⟨hne, sym, xs, i, j, hxs, hxi, hyj⟩
  refine ⟨fun hxy => hne (e.injective hxy),
    sym, e ∘ xs, i, j, ?_, ?_, ?_⟩
  · exact (e.graph.map_rel_iff sym xs).2 hxs
  · exact congrArg e hxi
  · exact congrArg e hyj

/-- Map an actually surviving source vertex through an embedding
to a vertex surviving deletion of the embedded whole cut. -/
def fullFunctionalEmbedding_outsideCut
    {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B)
    (T : Set V) (x : {v : V // v ∉ T}) :
    {w : W // w ∉ e '' T} :=
  ⟨e x.1, by
    rintro ⟨z, hz, heq⟩
    have hxz : z = x.1 := e.injective heq
    exact x.2 (hxz ▸ hz)⟩

/-- Every source path avoiding an arbitrary vertex cut maps
to a path avoiding the full EMBEDDED cut. No homomorphism
of forbidden sources or target-image quotient is involved. -/
theorem fullFunctionalEmbedding_reachOutside_map
    {V W : Type v}
    {A : Structure L V} {B : Structure L W}
    (e : Structure.Embedding A B)
    (T : Set V)
    {x y : {v : V // v ∉ T}}
    (h : ReachOutside A.graph T x y) :
    ReachOutside B.graph (e '' T)
      (fullFunctionalEmbedding_outsideCut e T x)
      (fullFunctionalEmbedding_outsideCut e T y) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpath hedge ih =>
      have hStep : outsideAdjacency B.graph (e '' T)
          (fullFunctionalEmbedding_outsideCut e T _)
          (fullFunctionalEmbedding_outsideCut e T _) :=
        fullFunctionalEmbedding_gaifmanEdge_map e hedge
      exact ih.tail hStep

/-- The old EXTERIOR source component, when private to the
unchanged right-hand complement, survives an inner native
functional free-amalgam replacement as an EXACT component after
deleting the transported old outer root iRight(T).

Importantly T need NOT contain the inner gluing-root image.
The complete generated external boundary also remains exactly
iRight(T), not just its direct Gaifman-neighbourhood subset. -/
theorem fullFreeAmalgam_exteriorComponent_preserved_at_oldRoot
    {H E F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (T : Set F)
    (x : {b : F // b ∉ T})
    (hPrivate :
      componentFrom Right.graph T x ⊆ {b : F | b ∉ Set.range sR})
    (hBoundary :
      Right.functionClosure
        (gaifmanNeighborhood Right.graph
          (componentFrom Right.graph T x)) = T) :
    componentFrom Whole.graph (iR '' T)
      (fullFunctionalEmbedding_outsideCut iR T x) =
        iR '' componentFrom Right.graph T x ∧
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph
          (iR '' componentFrom Right.graph T x)) = iR '' T := by
  let C : Set F := componentFrom Right.graph T x
  have hFullBoundary :
      Whole.functionClosure
        (gaifmanNeighborhood Whole.graph (iR '' C)) =
        iR '' T := by
    have hFull :=
      fullFreeAmalgam_private_generatedBoundary_eq_image
        hFree (Set.range sR) C
        (fun r => ⟨r, rfl⟩) hPrivate
    rw [hBoundary] at hFull
    exact hFull
  have hN : gaifmanNeighborhood Whole.graph (iR '' C) ⊆
      iR '' T := by
    intro z hz
    rw [← hFullBoundary]
    exact Whole.subset_functionClosure
      (gaifmanNeighborhood Whole.graph (iR '' C)) hz
  have hBase : iR x.1 ∈ iR '' C := by
    exact ⟨x.1, componentFrom_root Right.graph T x, rfl⟩
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨_hzNot, hzPath⟩ := hz
      exact reachOutside_stays_in_avoid_boundary
        Whole.graph (iR '' T) (iR '' C)
        (fullFunctionalEmbedding_outsideCut iR T x)
        hBase hN hzPath
    · rintro z ⟨b, hbC, rfl⟩
      obtain ⟨hbNotT, hbPath⟩ := hbC
      have hbMap : ReachOutside Whole.graph (iR '' T)
          (fullFunctionalEmbedding_outsideCut iR T x)
          (fullFunctionalEmbedding_outsideCut iR T ⟨b, hbNotT⟩) :=
        fullFunctionalEmbedding_reachOutside_map iR T hbPath
      exact ⟨(fullFunctionalEmbedding_outsideCut iR T
        ⟨b, hbNotT⟩).2, hbMap⟩
  · exact hFullBoundary

end AllThoseRamseyClasses.Lifts
