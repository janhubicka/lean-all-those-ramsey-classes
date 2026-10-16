import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import AllThoseRamseyClasses.Lifts.NormalizedFunctionalFlip

/-!
# Canonical lift witnesses in an enumerated full functional root chart

Fix a FULL functional root structure Root on any carrier U, together
with an ORDERED bijective enumeration `rho : Fin n ≃ U`.
Each root extension has the rooted-pattern presentation with roots
`P.rootEmbedding (rho i)`. The family of representatives of one
canonical incompatibility class is the new n-ary relation of a
function-preserving lift.

Occurrence of that relation provides exactly the replacement data
needed for a flip: an equivalent root extension Q and a weak (EHN)
realization whose enumerated root image is the prescribed tuple.

The canonical predicate explicitly requires INJECTIVE root images.
The manuscript's general weak homomorphism-embedding does not
automatically supply this. The old root's carrier may be a closed
separator subtype, not necessarily Fin n; the enumeration handles
that without identifying arbitrary carriers definitionally.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ} {U : Type v}
variable (Root : Structure L U) (rho : Fin n ≃ U)

/-- Forget the full root chart but preserve its ORDERED enumeration. -/
def FunctionalRootExtension.toEnumeratedRootedPattern
    (P : FunctionalRootExtension Root) :
    FunctionalRootedPattern.{u,v} L n where
  Carrier := P.Carrier
  str := P.str
  root := fun i => P.rootEmbedding (rho i)
  root_injective := P.rootEmbedding.injective.comp rho.injective

/-- All rooted presentations of extensions equivalent to P over
the SAME full root; complements range over ALL root extensions. -/
def enumeratedRootPieceClass
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root) :
    Set (FunctionalRootedPattern.{u,v} L n) :=
  {T | ∃ Q : FunctionalRootExtension Root,
    (functionalRootPieceSetoid Root F).r P Q ∧
      T = Q.toEnumeratedRootedPattern rho}

/-- A single new relation symbol of exactly the enumerated root arity. -/
def enumeratedRootClassLanguage (L : Language.{u}) (n : ℕ) :
    Language.{u} :=
  functionalLiftLanguage L PUnit.{u} (fun _ => n)

/-- Canonical lift with the n-ary predicate of P's piece-equivalence
class. Every original relation and function is left unchanged. -/
def enumeratedRootClassCanonicalLift
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W) :
    Structure (enumeratedRootClassLanguage L n) W :=
  functionalCanonicalLiftOn L PUnit.{u} (fun _ => n)
    (fun _ => enumeratedRootPieceClass Root rho F P) A

/-- Exact semantics: an extra relation tuple belongs iff it is
injective and an equivalent full-root piece has a weak realization
mapping its i-th ENUMERATED root to the i-th target vertex. -/
theorem enumeratedRootClassCanonicalRelation_iff
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W)
    (xs : Fin n → W) :
    (enumeratedRootClassCanonicalLift Root rho F P A).rel
      (.inr PUnit.unit) xs ↔
      Function.Injective xs ∧
        ∃ Q : FunctionalRootExtension Root,
          (functionalRootPieceSetoid Root F).r P Q ∧
            ∃ f : Q.Carrier → W,
              Q.str.IsEHNHomomorphismEmbedding A f ∧
              ∀ i : Fin n,
                f (Q.rootEmbedding (rho i)) = xs i := by
  constructor
  · intro h
    change FunctionalCanonicalExtraRelation L PUnit.{u}
      (fun _ => n)
      (fun _ => enumeratedRootPieceClass Root rho F P)
      A PUnit.unit xs at h
    obtain ⟨hinj, T, ⟨Q, hPQ, hT⟩, ⟨f, hf, hroot⟩⟩ := h
    subst T
    exact ⟨hinj, Q, hPQ, f, hf, hroot⟩
  · rintro ⟨hinj, Q, hPQ, f, hf, hroot⟩
    change FunctionalCanonicalExtraRelation L PUnit.{u}
      (fun _ => n)
      (fun _ => enumeratedRootPieceClass Root rho F P)
      A PUnit.unit xs
    refine ⟨hinj, Q.toEnumeratedRootedPattern rho,
      ⟨Q, hPQ, rfl⟩, ?_⟩
    exact ⟨f, hf, hroot⟩

/-- An original weak rooted realization with an EXPLICITLY injective
image of its enumerated root produces the canonical class predicate. -/
theorem enumeratedRootClassCanonicalRelation_of_weak
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W)
    (f : P.Carrier → W)
    (hf : P.str.IsEHNHomomorphismEmbedding A f)
    (hroots : Function.Injective
      (fun i : Fin n => f (P.rootEmbedding (rho i)))) :
    (enumeratedRootClassCanonicalLift Root rho F P A).rel
      (.inr PUnit.unit)
      (fun i : Fin n => f (P.rootEmbedding (rho i))) := by
  apply (enumeratedRootClassCanonicalRelation_iff Root rho F P A
    (fun i : Fin n => f (P.rootEmbedding (rho i)))).mpr
  refine ⟨hroots, P, ?_, f, hf, ?_⟩
  · rfl
  · intro i
    rfl

/-- The canonical class relation can be transported from one witness
to another. Its membership on the second tuple supplies a weak map
on an EQUIVALENT replacement piece, with exact ordered roots. -/
theorem enumeratedRootClassCanonicalWitness_from_other_lift
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W Z : Type v}
    (A : Structure L W) (B : Structure L Z)
    (fA : P.Carrier → W)
    (hfA : P.str.IsEHNHomomorphismEmbedding A fA)
    (hrootA : Function.Injective
      (fun i : Fin n => fA (P.rootEmbedding (rho i))))
    (xsB : Fin n → Z)
    (hSameRelation :
      (enumeratedRootClassCanonicalLift Root rho F P A).rel
        (.inr PUnit.unit)
        (fun i : Fin n => fA (P.rootEmbedding (rho i))) →
      (enumeratedRootClassCanonicalLift Root rho F P B).rel
        (.inr PUnit.unit) xsB) :
    Function.Injective xsB ∧
      ∃ Q : FunctionalRootExtension Root,
        (functionalRootPieceSetoid Root F).r P Q ∧
          ∃ f : Q.Carrier → Z,
            Q.str.IsEHNHomomorphismEmbedding B f ∧
            ∀ i : Fin n,
              f (Q.rootEmbedding (rho i)) = xsB i := by
  have hRelA := enumeratedRootClassCanonicalRelation_of_weak
    Root rho F P A fA hfA hrootA
  exact (enumeratedRootClassCanonicalRelation_iff
    Root rho F P B xsB).mp (hSameRelation hRelA)

/-- Surjectivity of the enumeration converts equality at ALL ordered
root coordinates into equality at EVERY vertex of the full root.
This is the compatibility condition required by an actual-source
free-amalgam fold, not merely tuple-wise compatibility by fiat. -/
theorem enumeratedRootMap_agrees_on_full_root
    {W : Type v} (P : FunctionalRootExtension Root)
    (f : P.Carrier → W) (g : U → W)
    (h : ∀ i : Fin n, f (P.rootEmbedding (rho i)) = g (rho i)) :
    ∀ r : U, f (P.rootEmbedding r) = g r := by
  intro r
  obtain ⟨i, rfl⟩ := rho.surjective r
  exact h i

end AllThoseRamseyClasses.Lifts
