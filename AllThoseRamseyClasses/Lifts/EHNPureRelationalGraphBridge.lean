import AllThoseRamseyClasses.Lifts.EHNRelationalGraphFiveCycleHE
import PartiteConstruction.Structure.FreeAmalgamationClass
import PartiteConstruction.Structure.Relationalize

/-!
# Track D: pure-relational native irreducibility and graph HE equivalence

When L has NO native function symbols, universal irreducibility for
Structure is equivalent to complete-Gaifman irreducibility of its
relational graph. The nontrivial direction is established here:
if two distinct vertices never occur together in any positive
relation tuple, split the whole source into the two FULL induced
complements of those vertices. Since there are no functions, these
sides are automatically closed and their union is a genuine FULL
free amalgam over their intersection. An irreducible full source
cannot cross both sides.

Consequently a RELATIONAL graph homomorphism-embedding produces a
genuine native IsEHNHomomorphismEmbedding in function-free languages:
irreducible native full tests have irreducible relational graphs;
the relational HE embeds those tests, and graph embeddings are
native FULL embeddings because there are no function fibres.

Applying this to the verified C5 colouring yields the exact native
EHN map into the triangle-with-T target with a noninjective pair
of genuine source separator roots. The *family closure under
tuple-surjective HE images* remains an independent obligation
before this is a fully formalized counterexample to the printed
blanket injectivization implication.

No claim about full maximal-lift free-amalgamation is made.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} [IsEmpty L.FuncSymbol]

/-- In a language with **no function symbols**, an irreducible
native full structure has complete Gaifman graph. Any pair
missing from all source relation tuples would yield a genuine
native full free decomposition into the two vertex-deletion
substructures. -/
theorem graph_irreducible_of_nativeIrreducible_noFunctions
    {V : Type} (A : Structure L V)
    (hIrr : A.Irreducible) : A.graph.Irreducible := by
  classical
  intro a b hab
  by_contra hNoGraph
  have noBoth
      (R : L.RelSymbol)
      (xs : Fin (L.relArity R) → V)
      (hRel : A.rel R xs)
      (i j : Fin (L.relArity R))
      (hi : xs i = a) (hj : xs j = b) : False := by
    apply hNoGraph
    exact ⟨(.inl R), xs, i, j, hRel, hi, hj⟩
  let LS : Set V := {v | v ≠ a}
  let RS : Set V := {v | v ≠ b}
  let MS : Set V := LS ∩ RS
  have hLS : A.IsClosed LS := by
    intro F
    exact isEmptyElim F
  have hRS : A.IsClosed RS := by
    intro F
    exact isEmptyElim F
  have hMS : A.IsClosed MS := by
    intro F
    exact isEmptyElim F
  let Left : Structure L LS := A.induce LS hLS
  let Right : Structure L RS := A.induce RS hRS
  let Common : Structure L MS := A.induce MS hMS
  let sL : Structure.Embedding Common Left := {
    toFun := fun z => ⟨z.1, z.2.1⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z => (z : LS).1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F
      exact isEmptyElim F
  }
  let sR : Structure.Embedding Common Right := {
    toFun := fun z => ⟨z.1, z.2.2⟩
    injective := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z => (z : RS).1) h
    map_rel_iff := fun _ _ => Iff.rfl
    map_func := by
      intro F
      exact isEmptyElim F
  }
  let iL : Structure.Embedding Left A := A.inclusion LS hLS
  let iR : Structure.Embedding Right A := A.inclusion RS hRS
  have hFree : Structure.IsFreeAmalgam sL sR iL iR := by
    constructor
    · intro v
      by_cases hv : v = a
      · right
        refine ⟨⟨v, ?_⟩, rfl⟩
        intro hvb
        exact hab (hv.symm.trans hvb)
      · left
        exact ⟨⟨v, hv⟩, rfl⟩
    · intro x y
      constructor
      · intro hxy
        have hv : x.1 = y.1 := hxy
        let z : MS := ⟨x.1, ⟨x.2, by simpa [hv] using y.2⟩⟩
        refine ⟨z, rfl, ?_⟩
        exact Subtype.ext hv.symm
      · rintro ⟨z, rfl, rfl⟩
        rfl
    · intro R xs
      constructor
      · intro hRel
        by_cases hAllLeft : ∀ i, xs i ∈ LS
        · left
          exact ⟨(fun i => ⟨xs i, hAllLeft i⟩), hRel, rfl⟩
        · right
          push_neg at hAllLeft
          obtain ⟨i, hMissing⟩ := hAllLeft
          have hAtA : xs i = a := by
            by_contra hneq
            exact hMissing hneq
          have hAllRight : ∀ j, xs j ∈ RS := by
            intro j
            by_contra hMissingB
            have hAtB : xs j = b := by
              by_contra hneq
              exact hMissingB hneq
            exact noBoth R xs hRel i j hAtA hAtB
          exact ⟨(fun j => ⟨xs j, hAllRight j⟩), hRel, rfl⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
        · exact hx
        · exact hy
    · intro F
      exact isEmptyElim F
  rcases hIrr hFree (Structure.Embedding.id A) with hLeft | hRight
  · obtain ⟨x, hx⟩ := hLeft a
    have heq : a = x.1 := hx
    exact x.2 heq.symm
  · obtain ⟨x, hx⟩ := hRight b
    have heq : b = x.1 := hx
    exact x.2 heq.symm

/-- A homomorphism-embedding between RELATIONAL graph encodings is
also native EHN when the language has no native function symbols.
This bridge uses universal/native irreducibility rather than
silently identifying the two definitions. -/
theorem nativeEHN_of_relationalGraphHE_noFunctions
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hGraph : A.graph.IsHomomorphismEmbedding B.graph f) :
    A.IsEHNHomomorphismEmbedding B f := by
  constructor
  · constructor
    · intro R xs hRel
      exact hGraph.1 (.inl R) xs hRel
    · intro F
      exact isEmptyElim F
  · intro U E hIrred e
    have hEGraph : E.graph.Irreducible :=
      graph_irreducible_of_nativeIrreducible_noFunctions E hIrred
    obtain ⟨g, hg⟩ :=
      hGraph.after_irreducible_embedding hEGraph e.graph
    have hClosed : E.ClosedMap B g := by
      intro F
      exact isEmptyElim F
    let gNative : Structure.Embedding E B :=
      Structure.Embedding.ofGraphClosed g hClosed
    refine ⟨gNative, ?_⟩
    intro x
    exact hg x

end AllThoseRamseyClasses.Lifts

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- The finite five-cycle-to-triangle-with-T colouring is an
ACTUAL native EHN homomorphism-embedding, despite identifying
the two genuine source separator vertices 0 and 2. The
unrestricted printed forbidden-family image-closure assumption
is still a separate mathematical/Lean proof obligation. -/
theorem weakColor_nativeEHN :
    cycle5.IsEHNHomomorphismEmbedding
      triangleExtraTernary weakColor := by
  exact nativeEHN_of_relationalGraphHE_noFunctions
    cycle5 triangleExtraTernary weakColor
    weakColor_graphHomomorphismEmbedding

/-- This genuine native EHN witness collapses a source-root pair,
so no deduction of injectivity from the EHN definition alone
can justify the canonical distinct-root relation. -/
theorem nativeEHN_with_colliding_root :
    cycle5.IsEHNHomomorphismEmbedding
      triangleExtraTernary weakColor ∧
    weakColor (0 : Fin 5) = weakColor (2 : Fin 5) :=
  ⟨weakColor_nativeEHN, weakColor_root_collision⟩

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
