import Mathlib.Tactic

/-!
# Finite data for the coloured-C5 maximal-lift counterexample

These are COMPUTABLE RELATIONAL TABLE checks, not a claim that the
whole original native global-canonical-lift counterexample has already
been bridged into Lean. The accompanying audit gives that argument.

The finite EHN test checks positive preservation and full embeddings
on EVERY irreducible INDUCED source subset. Gaifman adjacency for a
source test is computed using tuples entirely contained in that test;
ambient tuples with outside coordinates do not count. A separate
six-vertex regression protects this distinction for ternary relations.

The language has two binary relations and one ternary relation.
All three forbidden sources have empty ternary relation.
Enumerations use List.finRange, not the choice-based Finset.toList.
No native_decide, added axiom, or admission is used. Exact-head Lean
CI is required before even these finite certificates are called checked.
-/

namespace AllThoseRamseyClasses.Lifts.ColoredFiveCycleMaximalLiftRegression

set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

structure Table (n : ℕ) where
  red : Fin n → Fin n → Bool
  blue : Fin n → Fin n → Bool
  ternary : Fin n → Fin n → Fin n → Bool

def edge {n : ℕ} (i j x y : Fin n) : Bool :=
  decide ((x = i ∧ y = j) ∨ (x = j ∧ y = i))

def cycle : Table 5 where
  red := fun x y => edge 0 1 x y || edge 1 2 x y || edge 2 3 x y
  blue := fun x y => edge 3 4 x y || edge 4 0 x y
  ternary := fun _ _ _ => false

def redTriangle : Table 3 where
  red := fun x y => decide (x ≠ y)
  blue := fun _ _ => false
  ternary := fun _ _ _ => false

def mixedTriangle : Table 3 where
  red := edge 0 1
  blue := fun x y => edge 0 2 x y || edge 1 2 x y
  ternary := fun _ _ _ => false

def leftSide : Table 3 where
  red := fun x y => decide (x ≠ y)
  blue := fun _ _ => false
  ternary := fun x y z => decide (x ≠ y ∧ y ≠ z ∧ z ≠ x)

def rightSide : Table 2 where
  red := fun _ _ => false
  blue := fun x y => decide (x ≠ y)
  ternary := fun _ _ _ => false

def amalgam : Table 4 where
  red := fun x y => decide (x.val < 3 ∧ y.val < 3 ∧ x ≠ y)
  blue := edge 0 3
  ternary := fun x y z => decide
    (x.val < 3 ∧ y.val < 3 ∧ z.val < 3 ∧ x ≠ y ∧ y ≠ z ∧ z ≠ x)

def fold : Fin 5 → Fin 4 := ![0, 1, 2, 0, 3]
def leftIn : Fin 3 → Fin 4 := ![0, 1, 2]
def rightIn : Fin 2 → Fin 4 := ![0, 3]

/-- Pair incidence in the structure INDUCED on S. Every coordinate
of a witnessing ternary tuple must belong to S. Explicit finite
lists keep the Boolean computation independent of classical choice. -/
def adjacentWithin {n : ℕ} (A : Table n) (S : Finset (Fin n))
    (x y : Fin n) : Bool :=
  decide (x ∈ S ∧ y ∈ S) &&
    (A.red x y || A.red y x || A.blue x y || A.blue y x ||
      (List.finRange n).any (fun z => decide (z ∈ S) &&
        (A.ternary x y z || A.ternary x z y || A.ternary y x z ||
          A.ternary y z x || A.ternary z x y || A.ternary z y x)))

/-- Ambient Gaifman incidence, used for paths after deleting vertices.
This is deliberately different from induced-test irreducibility. -/
def adjacent {n : ℕ} (A : Table n) (x y : Fin n) : Bool :=
  adjacentWithin A Finset.univ x y

def clique {n : ℕ} (A : Table n) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → adjacentWithin A S x y = true

instance {n : ℕ} (A : Table n) (S : Finset (Fin n)) :
    Decidable (clique A S) := by
  unfold clique
  infer_instance

def fullOn {n m : ℕ} (A : Table n) (B : Table m)
    (f : Fin n → Fin m) (S : Finset (Fin n)) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) ∧
  (∀ x ∈ S, ∀ y ∈ S,
    A.red x y = B.red (f x) (f y) ∧
    A.blue x y = B.blue (f x) (f y)) ∧
  (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    A.ternary x y z = B.ternary (f x) (f y) (f z))

instance {n m : ℕ} (A : Table n) (B : Table m)
    (f : Fin n → Fin m) (S : Finset (Fin n)) :
    Decidable (fullOn A B f S) := by
  unfold fullOn
  infer_instance

def finiteEHN {n m : ℕ} (A : Table n) (B : Table m)
    (f : Fin n → Fin m) : Prop :=
  (∀ x y, A.red x y = true → B.red (f x) (f y) = true) ∧
  (∀ x y, A.blue x y = true → B.blue (f x) (f y) = true) ∧
  (∀ x y z, A.ternary x y z = true →
    B.ternary (f x) (f y) (f z) = true) ∧
  (∀ S : Finset (Fin n), clique A S → fullOn A B f S)

instance {n m : ℕ} (A : Table n) (B : Table m)
    (f : Fin n → Fin m) : Decidable (finiteEHN A B f) := by
  unfold finiteEHN
  infer_instance

/-- The two concrete sides are full in the displayed four-point target. -/
theorem concrete_sides_full :
    fullOn leftSide amalgam leftIn Finset.univ ∧
    fullOn rightSide amalgam rightIn Finset.univ := by
  decide +kernel

/-- Exact finite EHN table check for the folded forbidden five-cycle. -/
theorem folded_cycle_passes_all_source_tests :
    finiteEHN cycle amalgam fold ∧ fold 0 = fold 3 := by
  decide +kernel

/-- Neither side admits ANY EHN map from any forbidden representative. -/
theorem leftSide_forbidden_free_table :
    (∀ f : Fin 5 → Fin 3, ¬ finiteEHN cycle leftSide f) ∧
    (∀ f : Fin 3 → Fin 3, ¬ finiteEHN redTriangle leftSide f) ∧
    (∀ f : Fin 3 → Fin 3, ¬ finiteEHN mixedTriangle leftSide f) := by
  decide +kernel

theorem rightSide_forbidden_free_table :
    (∀ f : Fin 5 → Fin 2, ¬ finiteEHN cycle rightSide f) ∧
    (∀ f : Fin 3 → Fin 2, ¬ finiteEHN redTriangle rightSide f) ∧
    (∀ f : Fin 3 → Fin 2, ¬ finiteEHN mixedTriangle rightSide f) := by
  decide +kernel

/-- Increasing finite reachability, with all new vertices avoiding a. -/
def reachWithout {n : ℕ} (A : Table n) (a x : Fin n) :
    ℕ → Finset (Fin n)
  | 0 => {x}
  | k + 1 =>
      let S := reachWithout A a x k
      S ∪ Finset.univ.filter
        (fun y => y ≠ a ∧ ∃ z ∈ S, adjacent A z y = true)

def noSingletonCut {n : ℕ} (A : Table n) : Prop :=
  ∀ a x y : Fin n, x ≠ a → y ≠ a → y ∈ reachWithout A a x n

instance {n : ℕ} (A : Table n) : Decidable (noSingletonCut A) := by
  unfold noSingletonCut
  infer_instance

/-- The native geometric-piece bridge is not silently asserted here. -/
theorem forbidden_sources_have_no_singleton_cut :
    noSingletonCut cycle ∧ noSingletonCut redTriangle ∧
    noSingletonCut mixedTriangle := by
  decide +kernel

/-- A quotient labelled by its least class representative. These
regressive idempotent maps enumerate precisely the 52 partitions. -/
def canonicalPartition (q : Fin 5 → Fin 5) : Prop :=
  (∀ i, q i ≤ i) ∧ (∀ i, q (q i) = q i)

instance (q : Fin 5 → Fin 5) : Decidable (canonicalPartition q) := by
  unfold canonicalPartition
  infer_instance

/-- Exact source-generated relational image. Unused labels are isolated.
Nested finite-range lists replace noncomputable finite-set enumeration. -/
def quotient (q : Fin 5 → Fin 5) : Table 5 where
  red := fun x y => (List.finRange 5).any (fun a =>
    (List.finRange 5).any (fun b =>
      decide (q a = x ∧ q b = y) && cycle.red a b))
  blue := fun x y => (List.finRange 5).any (fun a =>
    (List.finRange 5).any (fun b =>
      decide (q a = x ∧ q b = y) && cycle.blue a b))
  ternary := fun _ _ _ => false

/-- Fullness on source edges is a necessary EHN condition. For this
triangle-free source it also suffices: its irreducible tests have
at most two vertices and source/quotient ternary relations vanish. -/
def edgeFaithful (q : Fin 5 → Fin 5) : Prop :=
  ∀ x y : Fin 5, cycle.red x y = true ∨ cycle.blue x y = true →
    q x ≠ q y ∧
    cycle.red x y = (quotient q).red (q x) (q y) ∧
    cycle.blue x y = (quotient q).blue (q x) (q y)

instance (q : Fin 5 → Fin 5) : Decidable (edgeFaithful q) := by
  unfold edgeFaithful
  infer_instance

/-- Finite image-closure certificate. The arbitrary-carrier / optional
isolated-vertex reduction is proved in the accompanying audit note. -/
theorem all_canonical_images_contain_forbidden_table :
    ∀ q : Fin 5 → Fin 5, canonicalPartition q → edgeFaithful q →
      Function.Injective q ∨
      (∃ e : Fin 3 → Fin 5,
        fullOn redTriangle (quotient q) e Finset.univ) ∨
      (∃ e : Fin 3 → Fin 5,
        fullOn mixedTriangle (quotient q) e Finset.univ) := by
  decide +kernel

/-- Three ternary tuples whose external witnesses make {0,1,2}
a clique in the AMBIENT Gaifman graph, but not in the induced structure. -/
def externalTernarySource : Table 6 where
  red := fun _ _ => false
  blue := fun _ _ => false
  ternary := fun x y z => decide
    ((x = 0 ∧ y = 1 ∧ z = 3) ∨
      (x = 1 ∧ y = 2 ∧ z = 4) ∨
      (x = 0 ∧ y = 2 ∧ z = 5))

def externalTernaryTarget : Table 6 where
  red := fun _ _ => false
  blue := fun _ _ => false
  ternary := fun x y z => externalTernarySource.ternary x y z ||
    decide (x = 0 ∧ y = 1 ∧ z = 2)

/-- Regression for INDUCED irreducibility rather than ambient adjacency. -/
theorem ambient_clique_need_not_be_induced_irreducible :
    (∀ x ∈ ({0, 1, 2} : Finset (Fin 6)),
      ∀ y ∈ ({0, 1, 2} : Finset (Fin 6)), x ≠ y →
        adjacent externalTernarySource x y = true) ∧
      ¬ clique externalTernarySource ({0, 1, 2} : Finset (Fin 6)) := by
  decide +kernel

/-- The extra target tuple is not inside ANY true irreducible source
test. The old ambient-clique implementation incorrectly rejected this
identity EHN map. The revised induced-test predicate accepts it. -/
theorem adding_unprotected_ternary_tuple_preserves_EHN :
    finiteEHN externalTernarySource externalTernaryTarget id := by
  decide +kernel

end AllThoseRamseyClasses.Lifts.ColoredFiveCycleMaximalLiftRegression
