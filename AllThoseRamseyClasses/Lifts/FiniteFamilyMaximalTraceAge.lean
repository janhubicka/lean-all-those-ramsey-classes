import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalFiniteRestriction
import AllThoseRamseyClasses.Lifts.FiniteFamilyCanonicalTrace

/-!
# A hereditary age of finite maximal finite-family component traces

A canonical component lift is generally NOT hereditary: a rooted piece
realized in a superstructure need not be realized in its old-language
substructure. Therefore the correct finite lifted objects are FULL
induced traces of canonical lifts of finite forbidden-free *witnesses*
which are maximal along the displayed finite shadow, not necessarily
maximal on the whole witness carrier.

We describe membership with an EXACT relation reflection condition
and the actual old functional shadow. Every structure in the class is
finite, and the witness can also be taken finite. The witness is
maximal only against finite forbidden-free full extensions.

The key hereditary lemma below restricts the given witness along an
arbitrary full expanded embedding, rather than claiming that the
canonical lift of the smaller old shadow equals its induced trace.

This is the correct input for class-level strong amalgamation; the
amalgamation construction is not claimed in this module. The
original published arbitrary regular-family lift remains separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The original-language structure obtained by forgetting all
finite-family component predicates, without changing any old
partial/set-valued function fibre. -/
abbrev FiniteNamedTraceShadow
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V) : Structure L V :=
  functionalShadowBig L Family.ComponentTag
    (fun tag => tag.width Family) Y

/-- The finite class of maximal **induced canonical traces**.
Y has the actual old functional shadow; its new relation is exactly
the rooted-realization profile of the finite forbidden-free witness
W over a full embedded copy of the shadow. The witness is maximal
along this copy among finite forbidden-free full extensions.

No extra old-language closure or auxiliary relation assumptions
are smuggled into membership. -/
def IsFiniteNamedMaximalTrace
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {V : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) V) : Prop :=
  Finite V ∧
  ∃ (UW : Type) (W : Structure L UW),
    Finite UW ∧ AvoidsFiniteNamedEHN Family W ∧
    ∃ (iW : Structure.Embedding
      (FiniteNamedTraceShadow Family Y) W),
      FiniteNamedCanonicalMaximalAlong Family
        (fun {U : Type} (C : Structure L U) =>
          FiniteNamedFiniteForbiddenFree Family C) iW ∧
      ∀ (tag : Family.ComponentTag)
        (xs : Fin (tag.width Family) → V),
        Y.rel (.inr tag) xs ↔
          (finiteNamedClosedComponentFoldedLift Family W).rel
            (.inr tag) (iW ∘ xs)

/-- A finite canonical trace of a finite forbidden-free witness
which is maximal along its old root belongs to the expanded age.
The shadow is literally the original root, including nullary
functions and all output-value sets. -/
theorem finiteNamedCanonicalTrace_mem_age
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UW : Type}
    [Finite UX] [Finite UW]
    {X : Structure L UX} {W : Structure L UW}
    (iW : Structure.Embedding X W)
    (hAvoid : AvoidsFiniteNamedEHN Family W)
    (hMax : FiniteNamedCanonicalMaximalAlong Family
        (fun {U : Type} (C : Structure L U) =>
          FiniteNamedFiniteForbiddenFree Family C) iW) :
    IsFiniteNamedMaximalTrace Family
      (finiteNamedCanonicalTrace Family iW) := by
  refine ⟨inferInstance, UW, W, inferInstance, hAvoid, ?_⟩
  have hShadow :
      FiniteNamedTraceShadow Family
        (finiteNamedCanonicalTrace Family iW) = X :=
    finiteNamedCanonicalTrace_shadow Family iW
  subst hShadow
  refine ⟨iW, hMax, ?_⟩
  intro tag xs
  exact Iff.rfl

/-- Restrict an induced maximal finite-family lifted trace through
ANY FULL expanded embedding. In particular it is hereditary under
all finite substructures, not just canonical old-language images.
The same finite witness works for the smaller root. -/
theorem IsFiniteNamedMaximalTrace.of_embedding
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VB : Type}
    {A : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VA}
    {B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB}
    (hB : IsFiniteNamedMaximalTrace Family B)
    (e : Structure.Embedding A B) :
    IsFiniteNamedMaximalTrace Family A := by
  rcases hB with ⟨hFinB, UW, W, hFinW, hAvoid, iW, hMax, hBrel⟩
  letI : Finite VB := hFinB
  have hFinA : Finite VA :=
    Finite.of_injective e e.injective
  let shE : Structure.Embedding
      (FiniteNamedTraceShadow Family A)
      (FiniteNamedTraceShadow Family B) :=
    functionalShadowBigEmbedding L
      Family.ComponentTag (fun tag => tag.width Family) e
  have hMaxSmall :
      FiniteNamedCanonicalMaximalAlong Family
        (fun {U : Type} (C : Structure L U) =>
          FiniteNamedFiniteForbiddenFree Family C)
        (iW.comp shE) :=
    FiniteNamedCanonicalMaximalAlong.restrict_root
      Family
      (fun {U : Type} (C : Structure L U) =>
        FiniteNamedFiniteForbiddenFree Family C)
      iW shE hMax
  refine ⟨hFinA, UW, W, hFinW, hAvoid,
    iW.comp shE, hMaxSmall, ?_⟩
  intro tag xs
  have he := e.map_rel_iff (.inr tag) xs
  have hw := hBrel tag (shE ∘ xs)
  change B.rel (.inr tag) (shE ∘ xs) ↔
      A.rel (.inr tag) xs at he
  have h := he.symm.trans hw
  change A.rel (.inr tag) xs ↔
    (finiteNamedClosedComponentFoldedLift Family W).rel
      (.inr tag) ((iW.comp shE) ∘ xs)
  exact h

end AllThoseRamseyClasses.Lifts
