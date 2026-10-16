import AllThoseRamseyClasses.Lifts.FunctionalPieceIncidence
import AllThoseRamseyClasses.Lifts.ClosedComponentComplement
import PartiteConstruction.Structure.FreeAmalgam

/-!
# A genuine functional free-amalgam decomposition along a closed cut

Let R be function-closed, and C a whole component of the Gaifman
graph of A after deleting R. The induced functional structures
on R∪C and V\\C are both closed (already verified). They intersect
exactly in R, cover A, and no positive relation or function
incidence crosses the two exclusive sides.

This constructs the actual full four-embedding `IsFreeAmalgam`
certificate, NOT merely a relational graph representation. It is
the decomposition of a forbidden witness needed to replace one of
its rooted pieces in the Section 3 flip lemma.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Any inclusion of closed vertex sets induces a FULL embedding
between their exact induced functional substructures. -/
def closedSubsetEmbedding
    (A : Structure L V) {S T : Set V}
    (hS : A.IsClosed S) (hT : A.IsClosed T)
    (hST : S ⊆ T) :
    Structure.Embedding (A.induce S hS) (A.induce T hT) where
  toFun := fun x => ⟨x.1, hST x.2⟩
  injective := by
    intro x y h
    apply Subtype.ext
    exact congrArg Subtype.val h
  map_rel_iff := fun _ _ => Iff.rfl
  map_func := by
    intro F xs
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyS : y.1 ∈ S :=
        hS F (Subtype.val ∘ xs) (fun i => (xs i).2) hy
      exact ⟨⟨y.1, hyS⟩, hy, by apply Subtype.ext; rfl⟩

/-- The root has a full inclusion into its component side. -/
def componentRootToPiece
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.Embedding (A.induce R hR)
      (functionalComponentInduce A R hR root) :=
  closedSubsetEmbedding A hR
    (functionalComponentUnion_isClosed A R hR root)
    (by intro x hx; exact Or.inl hx)

/-- The root also has a full inclusion into the complementary side. -/
def componentRootToComplement
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.Embedding (A.induce R hR)
      (functionalComponentComplementInduce A R hR root) :=
  closedSubsetEmbedding A hR
    (functionalComponentComplement_isClosed A R hR root)
    (by
      intro x hx hC
      exact hC.1 hx)

/-- The structure A is exactly the full functional free amalgam of
the induced piece and its closed complement over the original root R.

The Boolean side localization does not assume that source and target
vertices are distinct except where a Gaifman edge is constructed.
Hence nullary functions and repeated tuple coordinates are included.
-/
theorem component_isFreeAmalgam
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R) (root : {v : V // v ∉ R}) :
    Structure.IsFreeAmalgam
      (componentRootToPiece A R hR root)
      (componentRootToComplement A R hR root)
      (functionalComponentEmbedding A R hR root)
      (functionalComponentComplementEmbedding A R hR root) := by
  let C : Set V := functionalComponentFrom A R root
  let Left : Set V := R ∪ C
  let Right : Set V := Set.compl C
  let AL : Structure L Left :=
    functionalComponentInduce A R hR root
  let AR : Structure L Right :=
    functionalComponentComplementInduce A R hR root
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    by_cases hzC : z ∈ C
    · left
      exact ⟨⟨z, Or.inr hzC⟩, rfl⟩
    · right
      exact ⟨⟨z, hzC⟩, rfl⟩
  · intro a b
    constructor
    · intro hab
      have hv : a.1 = b.1 := hab
      have haR : a.1 ∈ R := by
        rcases a.2 with haR | haC
        · exact haR
        · exact False.elim (b.2 (hv.symm ▸ haC))
      let d : R := ⟨a.1, haR⟩
      refine ⟨d, ?_, ?_⟩
      · apply Subtype.ext
        rfl
      · apply Subtype.ext
        exact hv.symm
    · rintro ⟨d, rfl, rfl⟩
      rfl
  · intro q t
    constructor
    · intro ht
      have hside :=
        gaifmanTuple_side_localization A.graph R root (.inl q) t ht
      rcases hside with hL | hR
      · left
        let xs : Fin (L.relArity q) → Left :=
          fun i => ⟨t i, hL i⟩
        refine ⟨xs, ?_, ?_⟩
        · exact ht
        · funext i
          rfl
      · right
        let xs : Fin (L.relArity q) → Right :=
          fun i => ⟨t i, hR i⟩
        refine ⟨xs, ?_, ?_⟩
        · exact ht
        · funext i
          rfl
    · rintro (⟨xs, hxs, rfl⟩ | ⟨xs, hxs, rfl⟩)
      · exact hxs
      · exact hxs
  · intro f xs y
    constructor
    · intro hy
      rcases functionalIncidence_side_localization A R root f xs y hy with
        ⟨hxs, hyL⟩ | ⟨hxs, hyR⟩
      · left
        let aa : Fin (L.funcArity f) → Left :=
          fun i => ⟨xs i, hxs i⟩
        let bb : Left := ⟨y, hyL⟩
        refine ⟨aa, bb, ?_, ?_, ?_⟩
        · exact hy
        · funext i
          rfl
        · rfl
      · right
        let aa : Fin (L.funcArity f) → Right :=
          fun i => ⟨xs i, hxs i⟩
        let bb : Right := ⟨y, hyR⟩
        refine ⟨aa, bb, ?_, ?_, ?_⟩
        · exact hy
        · funext i
          rfl
        · rfl
    · rintro (⟨aa, bb, hbb, hxs, hby⟩ | ⟨aa, bb, hbb, hxs, hby⟩)
      · rw [hxs, hby]
        exact hbb
      · rw [hxs, hby]
        exact hbb

end AllThoseRamseyClasses.Lifts
