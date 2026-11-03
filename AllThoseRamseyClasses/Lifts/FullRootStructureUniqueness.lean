import PartiteConstruction.Structure.Basic

/-!
# Complete functional root structures are determined by a common FULL image

Two full native embeddings with the SAME underlying vertex map into
ONE full functional source force their domain structures to be equal
on the nose, including every old relation tuple and each complete
set-valued function fibre, also for nullary functions.

This is the precise input needed at the end of original Section 3
Claim 2: the original ordered outer root and a recovered NEW
minimal-separator root may have the same ordered vertices in the
retained complement, but the global piece-setoid requires equality
of the entire root *structure* on Fin n, not just their ranges.

No weak-map quotient, forbidden-family membership, minimal-separator
assumption or root-width bound is used here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}}

/-- FULL functional embeddings into a common target having the same
vertex coordinates determine the same complete source structure.

Unlike equal positive weak maps, this also reflects every relation
and the entire value set of every function, including nullary ones. -/
theorem fullRootStructure_eq_of_same_full_image
    {R : Type v} {W : Type w}
    {A B : Structure L R} {C : Structure L W}
    (eA : Structure.Embedding A C)
    (eB : Structure.Embedding B C)
    (hAgree : ∀ r : R, eA r = eB r) :
    A = B := by
  have hRel : A.rel = B.rel := by
    funext Rel xs
    have hArgs : eA ∘ xs = eB ∘ xs := by
      funext i
      exact hAgree (xs i)
    apply propext
    calc
      A.rel Rel xs ↔ C.rel Rel (eA ∘ xs) :=
        (eA.map_rel_iff Rel xs).symm
      _ ↔ C.rel Rel (eB ∘ xs) := by rw [hArgs]
      _ ↔ B.rel Rel xs := eB.map_rel_iff Rel xs
  have hFunc : A.func = B.func := by
    funext Fn xs
    have hArgs : eA ∘ xs = eB ∘ xs := by
      funext i
      exact hAgree (xs i)
    apply Set.ext
    intro y
    have hA : y ∈ A.func Fn xs ↔
        eA y ∈ C.func Fn (eA ∘ xs) := by
      rw [← eA.map_func Fn xs]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨z, hz, heq⟩
        exact (eA.injective heq) ▸ hz
    have hB : y ∈ B.func Fn xs ↔
        eB y ∈ C.func Fn (eB ∘ xs) := by
      rw [← eB.map_func Fn xs]
      constructor
      · intro hy
        exact ⟨y, hy, rfl⟩
      · rintro ⟨z, hz, heq⟩
        exact (eB.injective heq) ▸ hz
    have hSame :
        (eA y ∈ C.func Fn (eA ∘ xs)) ↔
          eB y ∈ C.func Fn (eB ∘ xs) := by
      rw [hAgree y, hArgs]
    exact hA.trans (hSame.trans hB.symm)
  cases A with
  | mk relA funcA =>
    cases B with
    | mk relB funcB =>
      change relA = relB at hRel
      change funcA = funcB at hFunc
      cases hRel
      cases hFunc
      rfl

end AllThoseRamseyClasses.Lifts
