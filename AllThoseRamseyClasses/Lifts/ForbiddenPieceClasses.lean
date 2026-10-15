import AllThoseRamseyClasses.Lifts.RootedFreeGluing

/-!
# Myhill--Nerode classes of rooted forbidden pieces

This ties the abstract setoid `pieceSetoid` to actual rooted
free-gluing and forbidden-pattern membership, up to isomorphism.

At each fixed width n we restrict the left argument to a supplied
set `pieces` of valid geometric pieces; the right test argument
ranges over ALL rooted structures of the same width, including those
that are not themselves pieces. This asymmetry is essential in
Definition `def:incompatible` and `def:regular` of the 2019 paper.

The geometric predicate selecting exactly the minimal-separating-cut
pieces of connected forbidden structures is not yet constructed.
Consequently this is a reusable *conditional interface*, not a
certification of regularity for any particular forbidden family.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u
variable {L : RelLanguage.{u}}

/-- Piece equivalence at a fixed root width: two selected forbidden
pieces are equivalent exactly when their sets of incompatible
arbitrary rooted tests agree. -/
def forbiddenPieceSetoid
    (F : StructureClass.{u,0} (L := L))
    (n : ℕ) (pieces : Set (RootedPattern.{u,0} L n)) :
    Setoid {P : RootedPattern.{u,0} L n // P ∈ pieces} :=
  pieceSetoid (fun (P : {P : RootedPattern.{u,0} L n // P ∈ pieces})
    (T : RootedPattern.{u,0} L n) =>
      IncompatibleByFreeGluing F P.1 T)

/-- The semantic Myhill--Nerode criterion, with no unnecessary
quantification over forbidden-only tests. -/
theorem forbiddenPiece_equiv_iff
    (F : StructureClass.{u,0} (L := L))
    (n : ℕ) (pieces : Set (RootedPattern.{u,0} L n))
    (P Q : {P : RootedPattern.{u,0} L n // P ∈ pieces}) :
    (forbiddenPieceSetoid F n pieces).r P Q ↔
      ∀ T : RootedPattern.{u,0} L n,
        IncompatibleByFreeGluing F P.1 T ↔
          IncompatibleByFreeGluing F Q.1 T := by
  constructor
  · intro h T
    exact incompatible_iff_of_equiv h T
  · intro h
    exact equiv_of_incompatible_iff h

/-- The actual quotient type of piece classes at one width. -/
abbrev ForbiddenPieceClasses
    (F : StructureClass.{u,0} (L := L))
    (n : ℕ) (pieces : Set (RootedPattern.{u,0} L n)) :=
  Quotient (forbiddenPieceSetoid F n pieces)

/-- Regularity as printed: finitely many equivalence classes at EVERY
positive root width. No global bound on root widths is assumed. -/
def ForbiddenRegularByPieces
    (F : StructureClass.{u,0} (L := L))
    (pieces : ∀ n : ℕ, Set (RootedPattern.{u,0} L n)) : Prop :=
  ∀ n : ℕ, 0 < n → Finite (ForbiddenPieceClasses F n (pieces n))

/-- The abstract new-relation symbols of the paper's canonical lift:
a positive root width, followed by its incompatibility equivalence
class at that width. -/
abbrev ForbiddenPieceSymbol
    (F : StructureClass.{u,0} (L := L))
    (pieces : ∀ n : ℕ, Set (RootedPattern.{u,0} L n)) :=
  Σ n : {n : ℕ // 0 < n},
    ForbiddenPieceClasses F n.1 (pieces n.1)

/-- The arity of a new piece symbol is its root width. -/
def forbiddenPieceSymbolArity
    (F : StructureClass.{u,0} (L := L))
    (pieces : ∀ n : ℕ, Set (RootedPattern.{u,0} L n))
    (i : ForbiddenPieceSymbol F pieces) : ℕ :=
  i.1.1

theorem forbiddenPieceSymbolArity_pos
    (F : StructureClass.{u,0} (L := L))
    (pieces : ∀ n : ℕ, Set (RootedPattern.{u,0} L n))
    (i : ForbiddenPieceSymbol F pieces) :
    0 < forbiddenPieceSymbolArity F pieces i :=
  i.1.2

/-- The signature L⁺ with one new relation for each width-indexed
incompatibility class. The canonical *interpretation* will be filled
in only after the geometric piece predicate has been established. -/
def forbiddenPieceLanguage
    (L : RelLanguage.{u})
    (F : StructureClass.{u,0} (L := L))
    (pieces : ∀ n : ℕ, Set (RootedPattern.{u,0} L n)) :=
  language L (ForbiddenPieceSymbol F pieces)
    (forbiddenPieceSymbolArity F pieces)

end AllThoseRamseyClasses.Lifts
