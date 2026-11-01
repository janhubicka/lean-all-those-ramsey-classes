import AllThoseRamseyClasses.Lifts.EHNClosedRangeFactorization
import AllThoseRamseyClasses.Lifts.OriginalPartialWeakImageQuotient
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# Track D: faithful image-closure conclusion, and the missing tuple premise

The original 2019 Section 3 closure clause is NOT merely
  (surjective native EHN image of a forbidden source is forbidden).
It asks for an ORIGINAL tuple-surjective homomorphism-embedding
image to CONTAIN a FULL forbidden substructure.

We record this weaker, correctly shaped contract separately from
the stronger `hImageClosed` used by EHNInjectiveSupportMinimizer.
With a genuinely function-closed target range AND a separate
tuple-surjectivity witness for its FULL induced structure, the
range factorization does give a genuine injectively embedded
forbidden member in the ambient target.

Neither an arbitrary weak EHN map nor source input-test coverage
automatically supplies the required tuple-surjectivity: old target
relations can have extra tuples on the image. The source-generated
tuple-surjective weak quotient is NOT fully embedded in the target.
These open implications must not be silently assumed.

This is a sound CONDITIONAL transfer, not a proof of the
unrestricted printed injectivization sentence or strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A target contains a native FULL embedding of some forbidden
structure (rather than necessarily belonging to the family itself). -/
def ContainsFullForbiddenSubstructure
    (F : ∀ {X : Type}, Structure L X → Prop)
    {Y : Type} (Target : Structure L Y) : Prop :=
  ∃ (X : Type) (Src : Structure L X),
    F Src ∧ Nonempty (Structure.Embedding Src Target)

/-- An explicit paper-shaped image-closure clause.

We specify the original-partial function-domain version of
tuple-surjectivity, with NO vertex-surjectivity premise.
The EHN predicate
here is the native full-on-irreducible-tests representation;
a separate semantics bridge is needed if using exactly the
paper's IsOriginalPartialHomomorphismEmbedding instead.

Critically, the conclusion is CONTAINS a full forbidden
substructure, not that the entire image is forbidden. -/
def HasTupleSurjectiveForbiddenImageClosure
    (F : ∀ {X : Type}, Structure L X → Prop) : Prop :=
  ∀ {X Y : Type}
    (Src : Structure L X) (Dst : Structure L Y) (q : X → Y),
    F Src →
    Src.IsEHNHomomorphismEmbedding Dst q →
    OriginalPartialTupleSurjective Src Dst q →
    ContainsFullForbiddenSubstructure F Dst

/-- Valid passage from a CLOSED actual target image through a
paper-shaped tuple-surjective image-closure hypothesis.

The *separate* hTuple hypothesis is essential. A native EHN
map with closed range is not necessarily tuple-surjective
onto the actual induced range: extra target relation tuples
may be present. -/
theorem fullForbiddenSubstructure_of_closedTupleSurjectiveEHNRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {V W : Type}
    (Src : Structure L V) (Target : Structure L W)
    (f : V → W)
    (hForbidden : F Src)
    (hf : Src.IsEHNHomomorphismEmbedding Target f)
    (hClosed : Target.IsClosed (Set.range f))
    (hTuple : OriginalPartialTupleSurjective
      Src (Target.induce (Set.range f) hClosed)
      (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))) :
    ContainsFullForbiddenSubstructure F Target := by
  let S : Set W := Set.range f
  let Q : Structure L S := Target.induce S hClosed
  let q : V → S := fun x => ⟨f x, ⟨x, rfl⟩⟩
  obtain ⟨hqEHN, hqSurj⟩ :=
    ehn_closedRange_surjectiveInducedFactor Src Target f hf hClosed
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    hImage Src Q q hForbidden hqEHN hTuple
  exact ⟨Z, P, hP, ⟨(Target.inclusion S hClosed).comp e⟩⟩

/-- With finite forbidden sources, the same faithful image-closure
contract produces a genuine INJECTIVE forbidden EHN witness in the
target, but only when the actual induced image is tuple-surjective.

No source-support minimization or extra function-test cover is
assumed here; the missing hTuple remains visible. -/
theorem injectiveForbiddenWitness_of_closedTupleSurjectiveEHNRange
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {V W : Type}
    (Src : Structure L V) (Target : Structure L W)
    (f : V → W)
    (hForbidden : F Src)
    (hf : Src.IsEHNHomomorphismEmbedding Target f)
    (hClosed : Target.IsClosed (Set.range f))
    (hTuple : OriginalPartialTupleSurjective
      Src (Target.induce (Set.range f) hClosed)
      (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))) :
    ∃ w : ForbiddenEHNWitness F Target,
      Function.Injective w.toTarget := by
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    fullForbiddenSubstructure_of_closedTupleSurjectiveEHNRange
      F hImage Src Target f hForbidden hf hClosed hTuple
  let w : ForbiddenEHNWitness F Target := {
    Carrier := Z
    finiteCarrier := hFiniteF P hP
    source := P
    forbidden := hP
    toTarget := e
    homEmbedding := e.isEHNHomomorphismEmbedding
  }
  exact ⟨w, e.injective⟩

end AllThoseRamseyClasses.Lifts
