import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces
import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import AllThoseRamseyClasses.Lifts.RootedPatternIso

/-!
# Genuine functional pieces of a forbidden connected class

The functional rooted pattern of a geometric piece is the FULL
induced relation/function structure on the cut and one component,
with an ordered injective root tuple. The existing graph encoding
then gives exactly the relational rooted pattern exported by the
earlier verified geometry module.

A family of forbidden sources now determines a genuine set of
rooted functional pieces: the left side must arise, up to a FULL
root-preserving isomorphism, from a *finite member of the family*
with a minimal closed separating cut.

This removes the arbitrary candidate-piece parameter at the
geometric-selection layer. The further quotient by equal
incompatibility sets is separate from rooted isomorphism and from
the function-language rooted gluing theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Turn an actual function-rooted pattern into a relation-rooted
pattern via the existing function-graph language. A graph relation
for a function includes its input tuple and its output. -/
def functionalRootedGraph {n : ℕ}
    (P : FunctionalRootedPattern.{u,v} L n) :
    RootedPattern.{u,v} L.graph n where
  Carrier := P.Carrier
  str := P.str.graph
  root := P.root
  root_injective := P.root_injective

/-- Root-preserving FULL isomorphism of functional patterns is
captured by a full graph isomorphism, including preservation and
reflection of every actual function-value incidence. -/
abbrev FunctionalRootedPatternIso {n : ℕ}
    (P Q : FunctionalRootedPattern.{u,v} L n) : Type (max u (v+1)) :=
  RootedPatternIso (functionalRootedGraph P) (functionalRootedGraph Q)

/-- The rooted isomorphism relation is an actual equivalence on
the native functional rooted patterns. -/
def functionalRootedIsoSetoid (L : Language.{u}) (n : ℕ) :
    Setoid (FunctionalRootedPattern.{u,v} L n) where
  r P Q := Nonempty (FunctionalRootedPatternIso P Q)
  iseqv := {
    refl := by
      intro P
      exact ⟨RootedPatternIso.refl _⟩
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

/-- The genuinely selected functional rooted piece of a forbidden
structure, including the selected root order. -/
def geometricFunctionalRootedPattern
    {W : Type v} (A : Structure L W) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    FunctionalRootedPattern.{u,v} L n where
  Carrier := geometricPieceVertices A d
  str := geometricFunctionalPiece A d
  root := fun i => ⟨d.roots i, by
    change d.roots i ∈
      (Set.range d.roots ∪
        componentFrom A.graph (Set.range d.roots) d.left)
    exact Or.inl ⟨i, rfl⟩⟩
  root_injective := by
    intro i j h
    exact d.roots_injective (congrArg Subtype.val h)

/-- Native function-rooted and graph-rooted presentations have
literally the same carrier, roots and positive relation data. -/
theorem geometricFunctionalRootedPattern_graph
    {W : Type v} (A : Structure L W) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    functionalRootedGraph (geometricFunctionalRootedPattern A d) =
      geometricRootedGraphPiece A d := by
  rfl

/-- The *actual* width-n pieces obtained from finite forbidden
functional structures, invariant under full root-preserving
isomorphism. A family F is assumed to consist of connected
forbidden structures where the corresponding main theorem needs
that hypothesis; no connectedness is silently built into this
selection predicate. -/
def IsForbiddenGeometricFunctionalPiece
    (F : ∀ {W : Type v}, Structure L W → Prop)
    {n : ℕ} (P : FunctionalRootedPattern.{u,v} L n) : Prop :=
  ∃ (W : Type v) (A : Structure L W),
    Finite W ∧ F A ∧
      ∃ d : GeometricFunctionalPieceData A n,
        Nonempty (FunctionalRootedPatternIso P
          (geometricFunctionalRootedPattern A d))

/-- The set of actual root-width-n forbidden geometric pieces,
closed under the explicit full root-preserving isomorphism notion. -/
def forbiddenGeometricFunctionalPieces
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (n : ℕ) : Set (FunctionalRootedPattern.{u,v} L n) :=
  {P | IsForbiddenGeometricFunctionalPiece F P}

/-- Every selected piece has a finite source witness in the
original forbidden family; no abstract choice of representative
is used here. -/
theorem forbiddenGeometricFunctionalPieces_has_source
    (F : ∀ {W : Type v}, Structure L W → Prop)
    {n : ℕ} (P : FunctionalRootedPattern.{u,v} L n)
    (hP : P ∈ forbiddenGeometricFunctionalPieces F n) :
    ∃ (W : Type v) (A : Structure L W),
      Finite W ∧ F A ∧
        ∃ d : GeometricFunctionalPieceData A n,
          Nonempty (FunctionalRootedPatternIso P
            (geometricFunctionalRootedPattern A d)) :=
  hP

end AllThoseRamseyClasses.Lifts
