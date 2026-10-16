import AllThoseRamseyClasses.Lifts.RootedFreeGluing

/-!
# Root-preserving isomorphism of finite-width rooted patterns

This is the exact equivalence used in Section 3 ("Pieces") of
Hubička--Nešetřil (2019). Two rooted structures are isomorphic
only when a FULL relational isomorphism sends the i-th root
vertex to the i-th root vertex for every i. Equality of root sets,
or an unordered permutation of roots, is not sufficient.

The relation is an actual equivalence relation, with a Setoid for
quotienting geometric forbidden pieces by isomorphism. This
does not assert that different rooted isomorphism types are
`\sim_\mathcal F`-inequivalent: the latter is the coarser
Myhill--Nerode equivalence of identical incompatibility profiles.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v

/-- A structure isomorphism respecting the ORDERED root tuple. -/
structure RootedPatternIso
    {L : RelLanguage.{u}} {n : ℕ}
    (P Q : RootedPattern.{u,v} L n) where
  equiv : P.Carrier ≃ Q.Carrier
  rel_iff : ∀ R xs, Q.str.rel R (equiv ∘ xs) ↔ P.str.rel R xs
  roots : ∀ i, equiv (P.root i) = Q.root i

/-- Forget the inverse and root order to get an ordinary full embedding. -/
def RootedPatternIso.toEmbedding
    {L : RelLanguage.{u}} {n : ℕ}
    {P Q : RootedPattern.{u,v} L n}
    (e : RootedPatternIso P Q) :
    Embedding P.str Q.str where
  toFun := e.equiv
  injective := e.equiv.injective
  map_rel_iff := e.rel_iff

/-- The identity is a root-preserving isomorphism. -/
def RootedPatternIso.refl
    {L : RelLanguage.{u}} {n : ℕ}
    (P : RootedPattern.{u,v} L n) :
    RootedPatternIso P P where
  equiv := Equiv.refl P.Carrier
  rel_iff := by intro _ _; exact Iff.rfl
  roots := by intro _; rfl

/-- Root-preserving isomorphism is symmetric. -/
def RootedPatternIso.symm
    {L : RelLanguage.{u}} {n : ℕ}
    {P Q : RootedPattern.{u,v} L n}
    (e : RootedPatternIso P Q) :
    RootedPatternIso Q P where
  equiv := e.equiv.symm
  rel_iff := by
    intro R xs
    have h := (e.rel_iff R (e.equiv.symm ∘ xs)).symm
    have heq : e.equiv ∘ (e.equiv.symm ∘ xs) = xs := by
      funext i
      exact e.equiv.apply_symm_apply (xs i)
    simpa only [heq] using h
  roots := by
    intro i
    calc
      e.equiv.symm (Q.root i) =
          e.equiv.symm (e.equiv (P.root i)) := by rw [e.roots i]
      _ = P.root i := e.equiv.symm_apply_apply (P.root i)

/-- Root-preserving isomorphisms compose. -/
def RootedPatternIso.trans
    {L : RelLanguage.{u}} {n : ℕ}
    {P Q T : RootedPattern.{u,v} L n}
    (e : RootedPatternIso P Q)
    (f : RootedPatternIso Q T) :
    RootedPatternIso P T where
  equiv := e.equiv.trans f.equiv
  rel_iff := by
    intro R xs
    have h : (e.equiv.trans f.equiv) ∘ xs =
        f.equiv ∘ (e.equiv ∘ xs) := by
      funext i
      rfl
    rw [h]
    exact (f.rel_iff R (e.equiv ∘ xs)).trans (e.rel_iff R xs)
  roots := by
    intro i
    change f.equiv (e.equiv (P.root i)) = T.root i
    rw [e.roots i, f.roots i]

/-- The rooted isomorphism relation with equivalence proofs bundled
in a Setoid. It retains all negative relational information and
the precise order of the roots. -/
def rootedPatternIsoSetoid
    (L : RelLanguage.{u}) (n : ℕ) :
    Setoid (RootedPattern.{u,v} L n) where
  r P Q := Nonempty (RootedPatternIso P Q)
  iseqv := {
    refl := by intro P; exact ⟨RootedPatternIso.refl P⟩
    symm := by
      intro P Q h
      obtain ⟨e⟩ := h
      exact ⟨e.symm⟩
    trans := by
      intro P Q T hPQ hQT
      obtain ⟨e⟩ := hPQ
      obtain ⟨f⟩ := hQT
      exact ⟨e.trans f⟩
  }

end AllThoseRamseyClasses.Lifts
