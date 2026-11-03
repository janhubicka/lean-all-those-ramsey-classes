import AllThoseRamseyClasses.Published.FunctionalWithParts2019FixedPointFreeSingleton
import PartiteConstruction.Structure.PartialSetFunctionsWeakEmbedding

/-!
# Track C: singleton-vacuity persists under the survey's CLIPPED weak convention

The survey uses a clipped weak restriction instead of the
complete-fibre (all-or-none) weak restriction. The existing
fixed-point-free unary example had only tested the latter.

Here we prove a strictly stronger and convention-INDEPENDENT
obstruction: EVERY partial function structure on a POINTED
SUBSINGLETON carrier has no FULL embedding into a member of the
fixed-point-free unary H class. Neither the definition of the
weak operation nor the original source matters at all.

Apply the obstruction to the exact clipped weak singleton. Thus
a purported local test premise requiring a FULL H embedding for
every clipped weak test of cardinality <= 1 is also impossible for
a nonempty candidate, and so it can make a fixed-cutoff local-class
implication vacuous even with the survey's displayed weak convention.

The full original 2019 local-completion convention instead uses
positive homomorphism-embeddings protecting appropriate irreducible
copies; this lemma is not a counterexample to that corrected theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

universe w
variable {V X : Type w}

/-- For the fixed-point-free unary H-class, there is no full
genuinely partial functional embedding from ANY pointed
subsingleton carrier, regardless of the source operation's
definedness and whether its unique output is empty. -/
theorem fixedPointFreeUnary_noFullEmbedding_from_pointedSubsingleton
    [Subsingleton V] (v : V)
    (A : PartialSetStructure exampleLanguage V)
    (Target : PartialSetStructure exampleLanguage X)
    (partTarget : X → Fin 2)
    (hH : fixedPointFreeUnaryPartiteH Target partTarget) :
    ¬ Nonempty (PartialSetStructure.Embedding A Target) := by
  rintro ⟨e⟩
  let xs : Fin 1 → V := fun _ => v
  obtain ⟨y, hy, hY⟩ := hH (e.toFun v)
  have hArg : (e.toFun ∘ xs) =
      (fun _ : Fin 1 => e.toFun v) := by
    funext k
    fin_cases k
    rfl
  have hTarget : Target.func () (e.toFun ∘ xs) =
      some ({y} : Set X) :=
    (congrArg (Target.func ()) hArg).trans hY
  have hMap := e.map_func () xs
  have hMapTo : (A.func () xs).map
      (Structure.imageSet e.toFun) = some ({y} : Set X) :=
    hMap.trans hTarget
  cases hSource : A.func () xs with
  | none =>
      have hNone : (A.func () xs).map
          (Structure.imageSet e.toFun) = none :=
        congrArg
          (fun t : Option (Set V) =>
            t.map (Structure.imageSet e.toFun)) hSource
      have hImpossible : (none : Option (Set X)) = some {y} :=
        hNone.symm.trans hMapTo
      cases hImpossible
  | some U =>
      have hSome : (A.func () xs).map
          (Structure.imageSet e.toFun) =
          some (Structure.imageSet e.toFun U) :=
        congrArg
          (fun t : Option (Set V) =>
            t.map (Structure.imageSet e.toFun)) hSource
      have hImage : Structure.imageSet e.toFun U = ({y} : Set X) :=
        Option.some.inj (hSome.symm.trans hMapTo)
      have hyImage : y ∈ Structure.imageSet e.toFun U := by
        rw [hImage]
        simp
      obtain ⟨z, hz, hZ⟩ := hyImage
      have hzv : z = v := Subsingleton.elim z v
      exact hy (hZ.symm.trans (congrArg e.toFun hzv))

/-- The exact CLIPPED singleton weak restriction of ANY genuinely
partial unary source has no full embedding into ANY member of
the fixed-point-free unary class. The obstruction does not depend
on the old/whole-fibre domain-mask convention. -/
theorem fixedPointFreeUnary_noClippedWeakSingleton
    (A : PartialSetStructure exampleLanguage V) (x : V)
    {X : Type w} (Target : PartialSetStructure exampleLanguage X)
    (partTarget : X → Fin 2)
    (hH : fixedPointFreeUnaryPartiteH Target partTarget) :
    ¬ Nonempty
      (PartialSetStructure.Embedding (weakInduce A {x}) Target) := by
  let S : Set V := {x}
  letI : Subsingleton S := ⟨by
    intro a b
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.2).trans
      (Set.mem_singleton_iff.mp b.2).symm⟩
  exact fixedPointFreeUnary_noFullEmbedding_from_pointedSubsingleton
    (⟨x, Set.mem_singleton x⟩ : S)
    (weakInduce A S) Target partTarget hH

/-- The ALL-small-tests premise using FULL embeddings of the survey's
CLIPPED weak restrictions at cutoff 1 forces the candidate empty.
There is no inflation of test carriers and no isomorphism oracle. -/
theorem fixedPointFreeUnary_clippedAllSmall_forces_empty
    [Finite V] (A : PartialSetStructure exampleLanguage V)
    (hSmall : ∀ S : Finset V, S.card ≤ 1 →
      ∃ (X : Type w) (_ : Finite X)
        (Target : PartialSetStructure exampleLanguage X)
        (partTarget : X → Fin 2),
        fixedPointFreeUnaryPartiteH Target partTarget ∧
        Nonempty (PartialSetStructure.Embedding
          (weakInduce A (↑S : Set V)) Target)) :
    IsEmpty V := by
  classical
  refine ⟨fun x => ?_⟩
  obtain ⟨X, hFinite, Target, partTarget, hH, hEmb⟩ :=
    hSmall {x} (by simp)
  exact (fixedPointFreeUnary_noClippedWeakSingleton
    A x Target partTarget hH) hEmb

end AllThoseRamseyClasses.Published
