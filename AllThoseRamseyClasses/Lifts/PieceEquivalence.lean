import AllThoseRamseyClasses.Lifts.CanonicalPieces

/-!
# Piece equivalence by identical incompatibility profiles

The purely logical/Myhill--Nerode layer of Section sec:regular
(Definition def:regular).  A geometric incompatibility relation must
eventually be obtained from rooted free amalgams and the forbidden
family; no such construction is assumed or silently proved here.

The type of pieces is indexed by its root width.  This ensures that
equivalence classes never mix widths.  The paper's regularity condition
is finiteness of the quotient FOR EVERY POSITIVE WIDTH, not finiteness
of the entire set of pieces.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v

/-- The set of all rooted tests incompatible with a given piece. -/
def incompatibilityProfile {Piece : Type u} {Test : Type v}
    (bad : Piece → Test → Prop) (p : Piece) : Set Test :=
  {t | bad p t}

/-- Piece equivalence: equal sets of incompatible rooted tests,
exactly the defining equivalence of Section sec:regular once `bad`
has been identified with the paper's rooted free-amalgam obstruction. -/
def pieceSetoid {Piece : Type u} {Test : Type v}
    (bad : Piece → Test → Prop) : Setoid Piece where
  r p q := incompatibilityProfile bad p = incompatibilityProfile bad q
  iseqv := {
    refl := by intro p; rfl
    symm := by intro p q h; exact h.symm
    trans := by intro p q r hpq hqr; exact hpq.trans hqr
  }

/-- Equivalent pieces have identical compatibility behaviour against
every rooted test. The argument is independent of their presentations. -/
theorem incompatible_iff_of_equiv
    {Piece : Type u} {Test : Type v}
    {bad : Piece → Test → Prop}
    {p q : Piece}
    (h : (pieceSetoid bad).r p q) (t : Test) :
    bad p t ↔ bad q t := by
  have hmem : t ∈ incompatibilityProfile bad p ↔
      t ∈ incompatibilityProfile bad q := by
    rw [h]
  simpa [incompatibilityProfile] using hmem

/-- Conversely, equal answers to all rooted tests define exactly the
same piece class. -/
theorem equiv_of_incompatible_iff
    {Piece : Type u} {Test : Type v}
    {bad : Piece → Test → Prop}
    {p q : Piece}
    (h : ∀ t, bad p t ↔ bad q t) :
    (pieceSetoid bad).r p q := by
  apply Set.ext
  intro t
  exact h t

/-- The regularity condition for a family of width-indexed pieces.
Only positive widths are required, matching Definition def:regular. -/
def RegularByProfiles
    (Piece : ℕ → Type u) (Test : ℕ → Type v)
    (bad : ∀ n, Piece n → Test n → Prop) : Prop :=
  ∀ n, 0 < n → Finite (Quotient (pieceSetoid (bad n)))

end AllThoseRamseyClasses.Lifts
