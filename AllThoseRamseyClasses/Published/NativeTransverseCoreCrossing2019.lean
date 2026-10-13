import Mathlib.Tactic

/-!
# A two-coordinate core relation crossing two transverse line ranges

Adversarial regression for the conditional transverse two-copy completion
interface in NativeTwoTransverseCopyRoot2019. A vertex-exact A-letter
factorization of the OVERLAP of two different line copies does not make
their entire induced union into a free relational amalgam.

Consider the reflexive Boolean order B={false,true} with
R(false,false), R(false,true), R(true,true). Its coordinatewise
square B×B has R²(z,w) when both coordinates are related.
The two literal transversal line maps are
    L0(x)=(x,false),       L1(y)=(true,y).
Their parameter-coordinate sets are disjoint.

Take z=(false,false) in L0 but NOT L1, and
w=(true,true) in L1 but NOT L0. The genuine coordinatewise
core relation R²(z,w) holds. Thus there is a relational
tuple crossing the exclusive sides of the two ranges, and
these two exact range pieces do NOT form a free cover.

This is a self-contained matrix-level Lean regression of the
partite-power phenomenon, not a claim that arbitrary tests in a
full Hales--Jewett Picture reduce to two copies. No statement
about the truth of the corrected 2019 Theorem 2.18 follows.
-/

namespace AllThoseRamseyClasses.Published

/-- Reflexive two-element order, presented as a plain binary
relation to make the witness independent of ordered-type APIs. -/
def native2019_boolean_base_relation (x y : Bool) : Prop :=
  x = y ∨ (x = false ∧ y = true)

/-- The actual coordinatewise power relation on two Boolean
coordinates. -/
def native2019_boolean_core_relation
    (x y : Bool × Bool) : Prop :=
  native2019_boolean_base_relation x.1 y.1 ∧
  native2019_boolean_base_relation x.2 y.2

/-- Variable first coordinate, constant false second coordinate. -/
def native2019_boolean_line_left (x : Bool) : Bool × Bool :=
  (x, false)

/-- Constant true first coordinate, variable second coordinate. -/
def native2019_boolean_line_right (y : Bool) : Bool × Bool :=
  (true, y)

/-- Although the line maps are transverse, the coordinatewise core
has a relational tuple crossing their exclusive image pieces.
Consequently these ranges are NOT a free relational cover. -/
theorem native2019_transverse_two_line_core_crossing :
    ∃ z w : Bool × Bool,
      z ∈ Set.range native2019_boolean_line_left ∧
      w ∈ Set.range native2019_boolean_line_right ∧
      z ∉ Set.range native2019_boolean_line_right ∧
      w ∉ Set.range native2019_boolean_line_left ∧
      native2019_boolean_core_relation z w := by
  refine ⟨(false, false), (true, true), ⟨false, rfl⟩,
    ⟨true, rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    have h : (true : Bool) = false := congrArg Prod.fst hy
    cases h
  · rintro ⟨x, hx⟩
    have h : (false : Bool) = true := congrArg Prod.snd hx
    cases h
  · simp [native2019_boolean_core_relation,
      native2019_boolean_base_relation]

end AllThoseRamseyClasses.Published
