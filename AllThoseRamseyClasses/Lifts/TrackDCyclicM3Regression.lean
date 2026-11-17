import Mathlib.Tactic

/-!
Track D exact m=3 tables. The forbidden source has 13 vertices,
and the target of two decorated halves has 11. Source irreducible
tests consist of singleton and E-edge tests (the graph is triangle-free,
and D-arcs are E-supported). No source-wide injectivity is postulated.
The target T relation contains all distinct triples within each half.
This is a finite certificate only, not the full infinite construction.
-/
namespace AllThoseRamseyClasses.Lifts.TrackDCyclicM3Regression

set_option maxRecDepth 8192
set_option maxHeartbeats 10000000

structure Table (n : ℕ) where
  markC : Fin n → Bool
  markP : Fin n → Bool
  markQ : Fin n → Bool
  markStart : Fin n → Bool
  markEnd : Fin n → Bool
  E : Fin n → Fin n → Bool
  D : Fin n → Fin n → Bool
  T : Fin n → Fin n → Fin n → Bool

def cyclicEdge (u v : Fin 8) : Bool :=
  decide (u ≠ v ∧ 3 ≤ (v.val + 8 - u.val) % 8 ∧
    (v.val + 8 - u.val) % 8 ≤ 5)

def srcBase : Fin 13 → Fin 8 :=
  ![3,4,5,0,1,2,6,7,0,1,2,6,7]
def tgtBase : Fin 11 → Fin 8 :=
  ![0,0,1,2,6,7,0,1,2,6,7]

def sameSourceCopy (x y : Fin 13) : Bool :=
  !(decide (3 ≤ x.val ∧ x.val < 8 ∧ 8 ≤ y.val) ||
    decide (3 ≤ y.val ∧ y.val < 8 ∧ 8 ≤ x.val))
def arc13 (a b x y : Fin 13) : Bool := decide (x = a ∧ y = b)
def arc11 (a b x y : Fin 11) : Bool := decide (x = a ∧ y = b)

def original : Table 13 where
  markC := fun x => decide (x.val < 3)
  markP := fun x => decide (3 ≤ x.val ∧ x.val < 8)
  markQ := fun x => decide (8 ≤ x.val)
  markStart := fun x => decide (x = 4 ∨ x = 9)
  markEnd := fun x => decide (x = 7 ∨ x = 12)
  E := fun x y => sameSourceCopy x y && cyclicEdge (srcBase x) (srcBase y)
  D := fun x y =>
    arc13 4 6 x y || arc13 6 5 x y || arc13 5 7 x y ||
    arc13 9 11 x y || arc13 11 10 x y || arc13 10 12 x y
  T := fun _ _ _ => false

def sameTargetP (x y : Fin 11) : Bool :=
  decide (1 ≤ x.val ∧ x.val ≤ 5 ∧ 1 ≤ y.val ∧ y.val ≤ 5)
def sameTargetQ (x y : Fin 11) : Bool :=
  decide (6 ≤ x.val ∧ 6 ≤ y.val)

def decorated : Table 11 where
  markC := fun x => decide (x = 0)
  markP := fun x => decide (1 ≤ x.val ∧ x.val ≤ 5)
  markQ := fun x => decide (6 ≤ x.val)
  markStart := fun x => decide (x = 2 ∨ x = 7)
  markEnd := fun x => decide (x = 5 ∨ x = 10)
  E := fun x y =>
    decide ((x = 0 ∧ y ≠ 0) ∨ (y = 0 ∧ x ≠ 0)) ||
    ((sameTargetP x y || sameTargetQ x y) &&
      cyclicEdge (tgtBase x) (tgtBase y))
  D := fun x y =>
    arc11 2 4 x y || arc11 4 3 x y || arc11 3 5 x y ||
    arc11 7 9 x y || arc11 9 8 x y || arc11 8 10 x y
  T := fun x y z =>
    decide (x ≠ y ∧ y ≠ z ∧ z ≠ x) &&
    (decide (x.val ≤ 5 ∧ y.val ≤ 5 ∧ z.val ≤ 5) ||
      decide ((x = 0 ∨ 6 ≤ x.val) ∧
        (y = 0 ∨ 6 ≤ y.val) ∧ (z = 0 ∨ 6 ≤ z.val)))

def fold : Fin 13 → Fin 11 :=
  ![0,0,0,1,2,3,4,5,6,7,8,9,10]
def pairVertex (x y : Fin 13) (i : Fin 2) : Fin 13 :=
  if i = 0 then x else y

theorem source_triangle_free :
    ∀ x y z : Fin 13, x ≠ y → y ≠ z → z ≠ x →
      ¬ (original.E x y = true ∧ original.E y z = true ∧
         original.E z x = true) := by
  decide +kernel

theorem D_arcs_are_E_edges :
    ∀ x y : Fin 13, original.D x y = true → original.E x y = true := by
  decide +kernel

theorem source_singleton_tables_reflect :
    ∀ x : Fin 13,
      original.markC x = decorated.markC (fold x) ∧
      original.markP x = decorated.markP (fold x) ∧
      original.markQ x = decorated.markQ (fold x) ∧
      original.markStart x = decorated.markStart (fold x) ∧
      original.markEnd x = decorated.markEnd (fold x) ∧
      original.E x x = decorated.E (fold x) (fold x) ∧
      original.D x x = decorated.D (fold x) (fold x) ∧
      original.T x x x = decorated.T (fold x) (fold x) (fold x) := by
  decide +kernel

theorem source_E_edge_tables_reflect :
    ∀ x y : Fin 13, original.E x y = true →
      fold x ≠ fold y ∧
      (∀ i j : Fin 2,
        original.E (pairVertex x y i) (pairVertex x y j) =
          decorated.E (fold (pairVertex x y i)) (fold (pairVertex x y j)) ∧
        original.D (pairVertex x y i) (pairVertex x y j) =
          decorated.D (fold (pairVertex x y i)) (fold (pairVertex x y j))) ∧
      (∀ i j k : Fin 2,
        original.T (pairVertex x y i) (pairVertex x y j)
            (pairVertex x y k) =
          decorated.T (fold (pairVertex x y i))
            (fold (pairVertex x y j)) (fold (pairVertex x y k))) := by
  decide +kernel

theorem source_E_D_positive_preserved :
    (∀ x y : Fin 13,
      original.E x y = true → decorated.E (fold x) (fold y) = true) ∧
    (∀ x y : Fin 13,
      original.D x y = true → decorated.D (fold x) (fold y) = true) := by
  decide +kernel

theorem target_triangles_T_decorated :
    ∀ x y z : Fin 11,
      x ≠ y → y ≠ z → z ≠ x →
      decorated.E x y = true → decorated.E y z = true →
      decorated.E z x = true → decorated.T x y z = true := by
  decide +kernel

end AllThoseRamseyClasses.Lifts.TrackDCyclicM3Regression
