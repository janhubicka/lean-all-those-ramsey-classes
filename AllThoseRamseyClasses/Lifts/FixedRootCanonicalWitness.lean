import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import AllThoseRamseyClasses.Lifts.NormalizedFunctionalFlip

/-!
# Extracting a replacement piece from a canonical fixed-root lift

For a fixed FULL functional root structure on the standard ordered
carrier Fin n, every root extension has a rooted-pattern presentation.
The family of representatives of one canonical incompatibility class
can be used as the added n-ary relation of a functional lift.

An occurrence of that relation in the target provides EXACTLY the
data needed for the functional flip: a root extension in the same
canonical incompatibility class and a weak (2019/EHN) realization
whose ordered-root image is the prescribed tuple.

The image tuple is required to be injective by the canonical lift
predicate. It is *not* inferred from a general weak HE. Conversely,
a weak realization of the original piece with injective root image
produces the canonical relation. Thus equality of the canonical
added relation on an ordered root tuple in two ambient witnesses
implies existence of a replacement realizing piece in the second.

This is a fixed-full-root chart lemma. Normalization of arbitrary
minimal-cut roots into Fin n charts is a separate task.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {n : ℕ}
variable (Root : Structure L (Fin n))

/-- Forget the designated full root chart, keeping its ORDERED tuple. -/
def FunctionalRootExtension.toRootedPattern
    (P : FunctionalRootExtension Root) :
    FunctionalRootedPattern.{u,v} L n where
  Carrier := P.Carrier
  str := P.str
  root := P.rootEmbedding
  root_injective := P.rootEmbedding.injective

/-- All rooted presentations of pieces equivalent to P with the SAME
full functional root. The equivalence tests ALL rooted complements,
as required in the published canonical lift. -/
def fixedRootPieceClass
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root) :
    Set (FunctionalRootedPattern.{u,v} L n) :=
  {T | ∃ Q : FunctionalRootExtension Root,
    (functionalRootPieceSetoid Root F).r P Q ∧
      T = Q.toRootedPattern}

/-- A single relation symbol whose arity is the ordered root width. -/
def fixedRootClassLanguage
    (L : Language.{u}) (n : ℕ) : Language.{u} :=
  functionalLiftLanguage L PUnit.{u} (fun _ => n)

/-- Canonical lift containing the n-ary relation associated to the
single piece-equivalence class P, retaining all original functions. -/
def fixedRootClassCanonicalLift
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W) :
    Structure (fixedRootClassLanguage L n) W :=
  functionalCanonicalLiftOn L PUnit.{u} (fun _ => n)
    (fun _ => fixedRootPieceClass Root F P) A

/-- The exact meaning of the chosen canonical n-ary added relation.
No constraint is imposed that its realizing weak map be globally
injective, only that the ordered root image is injective. -/
theorem fixedRootClassCanonicalRelation_iff
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W)
    (xs : Fin n → W) :
    (fixedRootClassCanonicalLift Root F P A).rel (.inr PUnit.unit) xs ↔
      Function.Injective xs ∧
        ∃ Q : FunctionalRootExtension Root,
          (functionalRootPieceSetoid Root F).r P Q ∧
            ∃ f : Q.Carrier → W,
              Q.str.IsEHNHomomorphismEmbedding A f ∧
              ∀ i : Fin n, f (Q.rootEmbedding i) = xs i := by
  constructor
  · intro h
    change FunctionalCanonicalExtraRelation L PUnit.{u}
      (fun _ => n) (fun _ => fixedRootPieceClass Root F P)
      A PUnit.unit xs at h
    obtain ⟨hinj, T, ⟨Q, hPQ, hT⟩, ⟨f, hf, hroot⟩⟩ := h
    subst T
    exact ⟨hinj, Q, hPQ, f, hf, hroot⟩
  · rintro ⟨hinj, Q, hPQ, f, hf, hroot⟩
    change FunctionalCanonicalExtraRelation L PUnit.{u}
      (fun _ => n) (fun _ => fixedRootPieceClass Root F P)
      A PUnit.unit xs
    refine ⟨hinj, Q.toRootedPattern, ⟨Q, hPQ, rfl⟩, ?_⟩
    exact ⟨f, hf, hroot⟩

/-- An original weak realization with an explicitly injective root
image produces the canonical class relation in its ambient target. -/
theorem fixedRootClassCanonicalRelation_of_weak
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W : Type v} (A : Structure L W)
    (f : P.Carrier → W)
    (hf : P.str.IsEHNHomomorphismEmbedding A f)
    (hroots : Function.Injective
      (fun i : Fin n => f (P.rootEmbedding i))) :
    (fixedRootClassCanonicalLift Root F P A).rel (.inr PUnit.unit)
      (fun i : Fin n => f (P.rootEmbedding i)) := by
  apply (fixedRootClassCanonicalRelation_iff Root F P A
    (fun i : Fin n => f (P.rootEmbedding i))).mpr
  refine ⟨hroots, P, ?_, f, hf, ?_⟩
  · exact (functionalRootPieceSetoid Root F).refl P
  · intro i
    rfl

/-- Equality of the class relation on one tuple in A and B transfers
a rooted realization from A to a suitable equivalent replacement
piece in B, with EXACT agreement of the ordered root tuple. -/
theorem fixedRootClassCanonicalRelation_transfer
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W Z : Type v}
    (A : Structure L W) (B : Structure L Z)
    (xsA : Fin n → W) (xsB : Fin n → Z)
    (hA : (fixedRootClassCanonicalLift Root F P A).rel
      (.inr PUnit.unit) xsA)
    (hB : (fixedRootClassCanonicalLift Root F P B).rel
      (.inr PUnit.unit) xsB) :
    Function.Injective xsA ∧
      Function.Injective xsB ∧
      ∃ Q : FunctionalRootExtension Root,
        (functionalRootPieceSetoid Root F).r P Q ∧
          ∃ f : Q.Carrier → Z,
            Q.str.IsEHNHomomorphismEmbedding B f ∧
            ∀ i : Fin n, f (Q.rootEmbedding i) = xsB i := by
  have hXA := (fixedRootClassCanonicalRelation_iff Root F P A xsA).mp hA
  have hXB := (fixedRootClassCanonicalRelation_iff Root F P B xsB).mp hB
  exact ⟨hXA.1, hXB.1, hXB.2⟩

/-- The useful specialized version: if a root tuple originally
realizes P in A and the SAME canonical lift relation is asserted
in B, a replacement piece Q exists with a weak map into B and
the prescribed roots. No arbitrary source-map injectivity is used. -/
theorem fixedRootClassCanonicalWitness_from_other_lift
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (P : FunctionalRootExtension Root)
    {W Z : Type v}
    (A : Structure L W) (B : Structure L Z)
    (fA : P.Carrier → W)
    (hfA : P.str.IsEHNHomomorphismEmbedding A fA)
    (hrootA : Function.Injective
      (fun i : Fin n => fA (P.rootEmbedding i)))
    (xsB : Fin n → Z)
    (hSameRelation :
      (fixedRootClassCanonicalLift Root F P A).rel
        (.inr PUnit.unit) (fun i : Fin n => fA (P.rootEmbedding i)) →
      (fixedRootClassCanonicalLift Root F P B).rel
        (.inr PUnit.unit) xsB) :
    Function.Injective xsB ∧
      ∃ Q : FunctionalRootExtension Root,
        (functionalRootPieceSetoid Root F).r P Q ∧
          ∃ f : Q.Carrier → Z,
            Q.str.IsEHNHomomorphismEmbedding B f ∧
            ∀ i : Fin n, f (Q.rootEmbedding i) = xsB i := by
  have hRelA := fixedRootClassCanonicalRelation_of_weak
    Root F P A fA hfA hrootA
  exact (fixedRootClassCanonicalRelation_iff Root F P B xsB).mp
    (hSameRelation hRelA)

end AllThoseRamseyClasses.Lifts
