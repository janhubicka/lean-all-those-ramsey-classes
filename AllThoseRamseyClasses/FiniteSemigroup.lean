import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Tactic

/-!
# Finite generation from finite positive-power ranges

A finite set of generators in a commutative semigroup generates a finite
subsemigroup whenever each generator has only finitely many positive powers.
The proof adjoins generators one at a time. The join of two subsemigroups
A and B has carrier A ∪ B ∪ AB, so the join of finite subsemigroups is finite.
No identity, cancellation, or finite ambient semigroup is assumed.

The result is about Mathlib's actual `Subsemigroup.closure`, hence exactly
nonempty products, including the empty generated subsemigroup when there
are no generators. There is no auxiliary zero-distance or empty product.
-/

namespace AllThoseRamseyClasses.FiniteSemigroup

universe u
variable {M : Type u}

/-- Index zero denotes the first positive power. -/
def positivePower [Mul M] (a : M) : ℕ → M
  | 0 => a
  | n + 1 => positivePower a n * a

/-- Products of positive powers are positive powers; an identity is unnecessary. -/
theorem positivePower_mul [Semigroup M] (a : M) (n k : ℕ) :
    positivePower a n * positivePower a k = positivePower a (n + k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change positivePower a n * (positivePower a k * a) =
        positivePower a (n + k + 1) * a
      rw [← mul_assoc, ih]

/-- Joining two finite subsemigroups of a commutative semigroup is finite. -/
theorem finite_sup [CommSemigroup M] (A B : Subsemigroup M)
    (hA : (A : Set M).Finite) (hB : (B : Set M).Finite) :
    ((A ⊔ B : Subsemigroup M) : Set M).Finite := by
  let J : Set M := (A : Set M) ∪ ((B : Set M) ∪
    Set.image2 (fun x y : M => x * y) (A : Set M) (B : Set M))
  have left : ∀ a ∈ A, ∀ x ∈ J, a * x ∈ J := by
    intro a ha x hx
    rcases hx with hx | hx | ⟨c, hc, d, hd, rfl⟩
    · exact Or.inl (A.mul_mem ha hx)
    · exact Or.inr (Or.inr ⟨a, ha, x, hx, rfl⟩)
    · exact Or.inr (Or.inr ⟨a * c, A.mul_mem ha hc, d, hd, mul_assoc _ _ _⟩)
  have right : ∀ b ∈ B, ∀ x ∈ J, b * x ∈ J := by
    intro b hb x hx
    rcases hx with hx | hx | ⟨c, hc, d, hd, rfl⟩
    · exact Or.inr (Or.inr ⟨x, hx, b, hb, mul_comm _ _⟩)
    · exact Or.inr (Or.inl (B.mul_mem hb hx))
    · exact Or.inr (Or.inr ⟨c, hc, b * d, B.mul_mem hb hd,
        by rw [mul_left_comm]⟩)
  let K : Subsemigroup M := {
    carrier := J
    mul_mem' := by
      intro x y hx hy
      rcases hx with hx | hx | ⟨a, ha, b, hb, rfl⟩
      · exact left x hx y hy
      · exact right x hx y hy
      · simpa only [mul_assoc] using left a ha (b * y) (right b hb y hy)
  }
  have hJK : (K : Set M).Finite :=
    hA.union (hB.union (Set.Finite.image2 (fun x y : M => x * y) hA hB))
  apply hJK.subset
  show A ⊔ B ≤ K
  exact sup_le (fun _ hx => Or.inl hx) (fun _ hx => Or.inr (Or.inl hx))

/-- A finite positive-power range contains the generated singleton subsemigroup. -/
theorem finite_closure_singleton [Semigroup M] (a : M)
    (ha : (Set.range (positivePower a)).Finite) :
    (Subsemigroup.closure ({a} : Set M) : Set M).Finite := by
  let P : Subsemigroup M := {
    carrier := Set.range (positivePower a)
    mul_mem' := by
      rintro _ _ ⟨n, rfl⟩ ⟨k, rfl⟩
      exact ⟨n + k + 1, (positivePower_mul a n k).symm⟩
  }
  apply ha.subset
  show Subsemigroup.closure ({a} : Set M) ≤ P
  apply Subsemigroup.closure_le.2
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  exact ⟨0, rfl⟩

/-- Finite positive-power ranges for finitely many commuting generators suffice
for finiteness of their actual generated subsemigroup. -/
theorem finite_closure [CommSemigroup M] (D : Set M) (hD : D.Finite)
    (hpower : ∀ a ∈ D, (Set.range (positivePower a)).Finite) :
    (Subsemigroup.closure D : Set M).Finite := by
  revert hpower
  refine Set.Finite.induction_on D hD ?_ ?_
  · intro _
    simp
  · intro a E _hnot _hE ih hpower
    have hsingle := finite_closure_singleton a (hpower a (Set.mem_insert a E))
    have hrest := ih (fun b hb => hpower b (Set.mem_insert_of_mem a hb))
    have hjoin := finite_sup (Subsemigroup.closure ({a} : Set M))
      (Subsemigroup.closure E) hsingle hrest
    apply hjoin.subset
    show Subsemigroup.closure (insert a E) ≤
      Subsemigroup.closure ({a} : Set M) ⊔ Subsemigroup.closure E
    apply Subsemigroup.closure_le.2
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact (show Subsemigroup.closure ({a} : Set M) ≤
          Subsemigroup.closure ({a} : Set M) ⊔ Subsemigroup.closure E from le_sup_left)
        (Subsemigroup.subset_closure (Set.mem_singleton a))
    · exact (show Subsemigroup.closure E ≤
          Subsemigroup.closure ({a} : Set M) ⊔ Subsemigroup.closure E from le_sup_right)
        (Subsemigroup.subset_closure hx)

end AllThoseRamseyClasses.FiniteSemigroup
