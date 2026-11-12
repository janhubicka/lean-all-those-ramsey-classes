import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track E2: a closed two-sided free cover detects native irreducibility

For genuine set-valued functions, free-amalgam side images are FULL
function-closed substructures. This gives a concrete cover test for
the universal native Structure.Irreducible predicate: if two closed
sets cover A and every relation tuple and every FUNCTION INCIDENCE
lies entirely on one side, one of the two sides must be all of A.

The proof constructs the actual full functional amalgam of the
induced closed sides over their closed intersection. It does not
replace functional irreducibility by ordinary Gaifman completeness
of the relational graph encoding, which would be false in general
(for example, a unary chain can force closure without a clique).
No finite carrier, singleton-valuedness, order, or positive arity
assumption is needed here.

This is the source-side lemma needed to derive U-irreducibility of
the canonical singleton-pattern tagged representation by the
verified U-closed-cover characterization.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A native irreducible structure admits no proper two-sided cover
by function-closed sets whose primitive relation tuples and complete
function incidence tuples are each supported on a single side.
Every fibre is genuinely set-valued, so the function condition covers
EACH output together with its entire primitive input tuple. -/
theorem nativeIrreducible_closedCover
    (A : Structure L V)
    (hA : A.Irreducible)
    (S T : Set V)
    (hS : A.IsClosed S)
    (hT : A.IsClosed T)
    (hCover : ∀ x : V, x ∈ S ∨ x ∈ T)
    (hRel : ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
      A.rel R xs →
      (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T))
    (hFunc : ∀ (F : L.FuncSymbol)
        (xs : Fin (L.funcArity F) → V) (y : V),
      y ∈ A.func F xs →
      ((∀ i, xs i ∈ S) ∧ y ∈ S) ∨
      ((∀ i, xs i ∈ T) ∧ y ∈ T)) :
    (∀ x : V, x ∈ S) ∨ (∀ x : V, x ∈ T) := by
  let I : Set V := S ∩ T
  have hI : A.IsClosed I := by
    intro F xs hxs y hy
    exact ⟨hS F xs (fun i => (hxs i).1) hy,
      hT F xs (fun i => (hxs i).2) hy⟩
  let Root : Structure L I := A.induce I hI
  let Left : Structure L S := A.induce S hS
  let Right : Structure L T := A.induce T hT
  let sL : Structure.Embedding Root Left := {
    toFun := fun a => ⟨a.1, a.2.1⟩
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
        have hyT : y.1 ∈ T :=
          hT F (Subtype.val ∘ xs)
            (fun i => (xs i).2.2) hy
        refine ⟨⟨y.1, ⟨y.2, hyT⟩⟩, hy, ?_⟩
        apply Subtype.ext
        rfl
  }
  let sR : Structure.Embedding Root Right := {
    toFun := fun a => ⟨a.1, a.2.2⟩
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
          hS F (Subtype.val ∘ xs)
            (fun i => (xs i).2.1) hy
        refine ⟨⟨y.1, ⟨hyS, y.2⟩⟩, hy, ?_⟩
        apply Subtype.ext
        rfl
  }
  let iL : Structure.Embedding Left A := Structure.inclusion A S hS
  let iR : Structure.Embedding Right A := Structure.inclusion A T hT
  have hFree : Structure.IsFreeAmalgam sL sR iL iR := by
    constructor
    · intro x
      rcases hCover x with hx | hx
      · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
      · exact Or.inr ⟨⟨x, hx⟩, rfl⟩
    · intro a b
      constructor
      · intro hab
        have hEq : a.1 = b.1 := hab
        have haT : a.1 ∈ T := by
          rw [hEq]
          exact b.2
        refine ⟨⟨a.1, ⟨a.2, haT⟩⟩, rfl, ?_⟩
        apply Subtype.ext
        exact hEq.symm
      · rintro ⟨d, rfl, rfl⟩
        rfl
    · intro R xs
      constructor
      · intro hx
        rcases hRel R xs hx with hSL | hTR
        · exact Or.inl ⟨(fun i => ⟨xs i, hSL i⟩), hx, rfl⟩
        · exact Or.inr ⟨(fun i => ⟨xs i, hTR i⟩), hx, rfl⟩
      · rintro (⟨args, h, rfl⟩ | ⟨args, h, rfl⟩)
        · exact h
        · exact h
    · intro F xs y
      constructor
      · intro hy
        rcases hFunc F xs y hy with ⟨hx, hyS⟩ | ⟨hx, hyT⟩
        · exact Or.inl
            ⟨(fun i => ⟨xs i, hx i⟩), ⟨y, hyS⟩,
              hy, rfl, rfl⟩
        · exact Or.inr
            ⟨(fun i => ⟨xs i, hx i⟩), ⟨y, hyT⟩,
              hy, rfl, rfl⟩
      · rintro (⟨args, out, hout, hxs, hy⟩ |
                ⟨args, out, hout, hxs, hy⟩)
        · rw [hxs, hy]
          exact hout
        · rw [hxs, hy]
          exact hout
  rcases hA hFree (Structure.Embedding.id A) with hAllS | hAllT
  · left
    intro x
    obtain ⟨a, ha⟩ := hAllS x
    have hx : x = a.1 := ha
    rw [hx]
    exact a.2
  · right
    intro x
    obtain ⟨b, hb⟩ := hAllT x
    have hx : x = b.1 := hb
    rw [hx]
    exact b.2

end AllThoseRamseyClasses.Published
