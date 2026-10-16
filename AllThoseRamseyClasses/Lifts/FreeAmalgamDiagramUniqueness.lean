import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold

/-!
# Uniqueness of FULL functional free-amalgam diagrams

Two full functional free-amalgam structures of the SAME two sides over
the SAME root are canonically isomorphic, identifying corresponding
side vertices. This is a genuine full isomorphism: it reflects all
positive and negative relations and preserves whole function fibres.

The proof uses only the previously verified arbitrary-source WEAK
functional fold in both directions. Each folded map is weakly
homomorphic; the two folds compose to the identity because the sides
cover both amalgams. Positivity in both directions together with
bijectivity then gives a full functional embedding.

This is an important bridge between the existential source-diagram
incompatibility predicate and the manuscript's canonical free gluing
up to isomorphism. No hereditary/isomorphism-closure hypothesis is
needed on any class of forbidden patterns.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F X Y : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {A : Structure L X} {B : Structure L Y}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left A}
variable {iR : Structure.Embedding Right A}
variable {jL : Structure.Embedding Left B}
variable {jR : Structure.Embedding Right B}

/-- The two full side diagrams determine an onto, induced
embedding between the whole amalgams that preserves both
inclusions on the nose. -/
theorem freeAmalgamDiagram_unique
    (hA : Structure.IsFreeAmalgam sL sR iL iR)
    (hB : Structure.IsFreeAmalgam sL sR jL jR) :
    ∃ e : Structure.Embedding A B,
      Function.Surjective e ∧
      (∀ a : E, e (iL a) = jL a) ∧
      (∀ b : F, e (iR b) = jR b) := by
  classical
  have hcB : ∀ r : H, jL (sL r) = jR (sR r) := by
    intro r
    exact (hB.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩
  have hcA : ∀ r : H, iL (sL r) = iR (sR r) := by
    intro r
    exact (hA.overlap (sL r) (sR r)).mpr ⟨r, rfl, rfl⟩
  let f : X → Y := compatibleFunctionalFold hA jL jR hcB
  let g : Y → X := compatibleFunctionalFold hB iL iR hcA
  have hfL (a : E) : f (iL a) = jL a :=
    compatibleFunctionalFold_left hA jL jR hcB a
  have hfR (b : F) : f (iR b) = jR b :=
    compatibleFunctionalFold_right hA jL jR hcB b
  have hgL (a : E) : g (jL a) = iL a :=
    compatibleFunctionalFold_left hB iL iR hcA a
  have hgR (b : F) : g (jR b) = iR b :=
    compatibleFunctionalFold_right hB iL iR hcA b
  have hgf : ∀ x : X, g (f x) = x := by
    intro x
    rcases hA.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · calc
        g (f x) = g (f (iL a)) := congrArg (fun z => g (f z)) ha
        _ = g (jL a) := congrArg g (hfL a)
        _ = iL a := hgL a
        _ = x := ha.symm
    · calc
        g (f x) = g (f (iR b)) := congrArg (fun z => g (f z)) hb
        _ = g (jR b) := congrArg g (hfR b)
        _ = iR b := hgR b
        _ = x := hb.symm
  have hfg : ∀ y : Y, f (g y) = y := by
    intro y
    rcases hB.covers y with ⟨a, ha⟩ | ⟨b, hb⟩
    · calc
        f (g y) = f (g (jL a)) := congrArg (fun z => f (g z)) ha
        _ = f (iL a) := congrArg f (hgL a)
        _ = jL a := hfL a
        _ = y := ha.symm
    · calc
        f (g y) = f (g (jR b)) := congrArg (fun z => f (g z)) hb
        _ = f (iR b) := congrArg f (hgR b)
        _ = jR b := hfR b
        _ = y := hb.symm
  have hfWeak : A.IsWeakHomomorphism B f :=
    (compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hA jL jR hcB
      jL.isEHNHomomorphismEmbedding
      jR.isEHNHomomorphismEmbedding).1
  have hgWeak : B.IsWeakHomomorphism A g :=
    (compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hB iL iR hcA
      iL.isEHNHomomorphismEmbedding
      iR.isEHNHomomorphismEmbedding).1
  let e : Structure.Embedding A B := {
    toFun := f
    injective := by
      intro x y hxy
      calc
        x = g (f x) := (hgf x).symm
        _ = g (f y) := congrArg g hxy
        _ = y := hgf y
    map_rel_iff := by
      intro R xs
      constructor
      · intro hrel
        have hback : A.rel R (g ∘ (f ∘ xs)) :=
          hgWeak.1 R (f ∘ xs) hrel
        have hcancel : g ∘ (f ∘ xs) = xs := by
          funext i
          exact hgf (xs i)
        simpa only [hcancel] using hback
      · exact hfWeak.1 R xs
    map_func := by
      intro F xs
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact hfWeak.2 F xs a ha
      · intro hy
        have hback : g y ∈ A.func F (g ∘ (f ∘ xs)) :=
          hgWeak.2 F (f ∘ xs) y hy
        have hcancel : g ∘ (f ∘ xs) = xs := by
          funext i
          exact hgf (xs i)
        rw [hcancel] at hback
        exact ⟨g y, hback, hfg y⟩
  }
  exact ⟨e, (fun y => ⟨g y, hfg y⟩), hfL, hfR⟩

end AllThoseRamseyClasses.Lifts
