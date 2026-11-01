import AllThoseRamseyClasses.Lifts.GlobalConnectedPositiveArityJEP

/-!
# Track F: a genuine native nullary obstruction to the printed JEP claim

The original Section 3 `mainthm` proof states that the age of maximal
F-lifts "clearly" has joint embedding. Under full embeddings, this can
fail if the native language admits even one nullary relation symbol.

For F = empty, the forbidden-avoidance class contains all native
finite structures. The singleton structures with opposite truth values
for one nullary relation R have NO common full target, because full
embedding reflects R on the unique nullary tuple.

The proof below constructs actual native functional structures and
derives a contradiction from genuine FULL embeddings. It does NOT
argue that the printed theorem is false if the intended language
convention prohibits nullary symbols. In positive-arity languages,
the independently proved connected-source JEP theorem applies.

This is a regression of ATRC-072 and never changes frozen ramsey.tex.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A full embedding reflects the truth value of an arity-zero relation,
independently of the source/target carriers. -/
theorem fullEmbedding_reflects_nullary_relation
    {VA VB : Type}
    {A : Structure L VA} {B : Structure L VB}
    (e : Structure.Embedding A B)
    (R : L.RelSymbol)
    (hZero : L.relArity R = 0)
    (xs : Fin (L.relArity R) → VA)
    (ys : Fin (L.relArity R) → VB) :
    A.rel R xs ↔ B.rel R ys := by
  have hTuple : (e ∘ xs) = ys := by
    funext i
    exact Fin.elim0 (Fin.cast hZero i)
  calc
    A.rel R xs ↔ B.rel R (e ∘ xs) :=
      (e.map_rel_iff R xs).symm
    _ ↔ B.rel R ys := by rw [hTuple]

/-- An actual one-vertex functional structure whose selected
nullary symbol holds. All other relation symbols are false and all
native partial-function fibres are empty. -/
def nullaryTrueUnitStructure (L : Language.{u})
    (R : L.RelSymbol) : Structure L Unit where
  rel := fun S _ => S = R
  func := fun _ _ => ∅

/-- A one-vertex functional structure with ALL relation symbols
false and all native partial-function fibres empty. -/
def nullaryFalseUnitStructure (L : Language.{u}) :
    Structure L Unit where
  rel := fun _ _ => False
  func := fun _ _ => ∅

/-- The two explicit finite structures disagree on R and hence
have NO common full functional embedding target. -/
theorem nullaryUnitStructures_noCommonFullTarget
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ ∃ (VT : Type) (Target : Structure L VT),
      ∃ (_eTrue : Structure.Embedding
          (nullaryTrueUnitStructure L R) Target)
        (_eFalse : Structure.Embedding
          (nullaryFalseUnitStructure L) Target), True := by
  rintro ⟨VT, Target, eTrue, eFalse, _⟩
  let xs : Fin (L.relArity R) → Unit := fun _ => ()
  have hAgreement :
      (nullaryTrueUnitStructure L R).rel R xs ↔
      (nullaryFalseUnitStructure L).rel R xs := by
    have hTrue :=
      fullEmbedding_reflects_nullary_relation eTrue R hZero xs
        (fun _ => ())
    have hFalse :=
      fullEmbedding_reflects_nullary_relation eFalse R hZero xs
        (fun _ => ())
    exact hTrue.trans hFalse.symm
  have hPositive :
      (nullaryTrueUnitStructure L R).rel R xs := by
    rfl
  have hNegative :
      (nullaryFalseUnitStructure L).rel R xs :=
    hAgreement.mp hPositive
  exact hNegative

/-- The truly empty forbidden family, so native EHN avoidance is
vacuous for EVERY finite structure. -/
def emptyGlobalForbiddenFamily (L : Language.{u}) :
    ∀ {V : Type}, Structure L V → Prop :=
  fun {_} _ => False

/-- The forbidden-free native class for the EMPTY family fails even
ordinary full JEP in the presence of a nullary relation.
This uses the exact `GlobalNativeFiniteJEP` interface, not a
hypothetical disagreement with a handwaved notion of embedding.

It does not claim a counterexample under a positive-arity language
convention, or to the separate corrected relational Theorem 2.18. -/
theorem emptyForbidden_nativeJEP_fails_of_nullaryRelation
    (L : Language.{u}) (R : L.RelSymbol)
    (hZero : L.relArity R = 0) :
    ¬ GlobalNativeFiniteJEP
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L) A) := by
  intro hJEP
  have hAllowedTrue :
      AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L)
        (nullaryTrueUnitStructure L R) := by
    intro U Source _ hForbidden
    exact False.elim hForbidden
  have hAllowedFalse :
      AvoidsGlobalFunctionalEHN (emptyGlobalForbiddenFamily L)
        (nullaryFalseUnitStructure L) := by
    intro U Source _ hForbidden
    exact False.elim hForbidden
  obtain ⟨VT, Target, _hFinite, _hAllowed, eTrue, eFalse, _⟩ :=
    hJEP (nullaryTrueUnitStructure L R)
      (nullaryFalseUnitStructure L)
      (inferInstance : Finite Unit)
      (inferInstance : Finite Unit)
      hAllowedTrue hAllowedFalse
  exact nullaryUnitStructures_noCommonFullTarget L R hZero
    ⟨VT, Target, eTrue, eFalse, True.intro⟩

end AllThoseRamseyClasses.Lifts
