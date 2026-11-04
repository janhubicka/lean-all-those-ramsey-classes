import AllThoseRamseyClasses.Lifts.EHNWeakImageExistentialTransport
import AllThoseRamseyClasses.Lifts.EHNFiveCycleTransportFailure

/-!
# Track D: a concrete irreducible test certifies failure of weak-image transport

Let w be an actual forbidden EHN witness into an arbitrary target.
The source-generated weak quotient Q is a *tuple-surjective*
original-partial homomorphism-embedding image of the forbidden
source. Consequently the printed image-closure clause gives
some FULL forbidden substructure P of Q.

If NO such full forbidden P embeds EHN into the ambient target,
the weak positive inclusion P -> Target itself cannot satisfy the
irreducible-test clause of EHN. Hence there is a genuine native
irreducible FULL substructure E of P, with a full embedding E -> P,
whose prescribed weak-inclusion coordinates have **no** full
embedding E -> Target.

Moreover this same irreducible test E cannot be lifted to a full
test of the original forbidden source with matching quotient
coordinates: a lift would give a full target embedding via the
original EHN witness. Thus the obstruction has TWO explicit
machine-checkable aspects, not merely an abstract negated predicate.

This local failed-test witness is the exact missing datum behind
the earlier incorrect inference that an incidence-generated
tuple-surjective quotient embeds FULLY into its original target.
It is NOT by itself a contradiction in the genuine maximal-lift
free-amalgam setting. A new geometric lemma would have to exclude
such tests or handle their root collisions by an alternative flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A forbidden full copy inside the source-generated weak image
contains a particular native irreducible test E that:
(1) has no full target embedding with the coordinates prescribed
by the weak inclusion, and
(2) has no full lift to the original forbidden source along the
tuple-surjective quotient.

This is an existential LOCAL obstruction, not an assumption
that the whole weak image is fully embeddable. -/
def HasForbiddenWeakImageBadIrreducibleTest
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target) : Prop :=
  ∃ (Z : Type) (P : Structure L Z),
    F P ∧
    ∃ (e : Structure.Embedding P
      (Structure.weakImage w.source Target w.toTarget))
      (U : Type) (E : Structure L U),
      E.Irreducible ∧
      ∃ (h : Structure.Embedding E P),
        (¬ ∃ g : Structure.Embedding E Target,
          ∀ x : U, g x = (e (h x)).1) ∧
        (¬ ∃ k : Structure.Embedding E w.source,
          ∀ x : U,
            Structure.weakImage.quotientMap
              (f := w.toTarget) (k x) = e (h x))

/-- Under EXACT printed tuple-surjective forbidden-family image
closure, absence of even ONE EHN-transportable forbidden full
copy in the weak quotient produces a specific irreducible
test whose image cannot be fully reflected in Target and
whose quotient coordinates do not lift fully to the source.

The proof never assumes the quotient's whole embedding is full,
nor demands tuple coverage of the FULL induced target range. -/
theorem forbiddenWeakImage_existsBadIrreducibleTest_of_noTransportableCopy
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target)
    (hNoCopy : ¬ HasTransportableForbiddenWeakImageCopy F Target w) :
    HasForbiddenWeakImageBadIrreducibleTest F Target w := by
  classical
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  let q : w.Carrier → Set.range w.toTarget :=
    Structure.weakImage.quotientMap (f := w.toTarget)
  obtain ⟨_, hqHE, hqTuple⟩ :=
    originalPartialHE_weakImage_quotient_data
      w.source Target w.toTarget
      w.homEmbedding.toOriginalPartial
  obtain ⟨Z, P, hP, ⟨e⟩⟩ :=
    hImage w.source Q q w.forbidden hqHE hqTuple
  have hWeak : P.IsWeakHomomorphism Target
      (fun z => (e z).1) :=
    (Structure.weakImage.inclusion_weak
      w.homEmbedding.1).comp e.isWeakHomomorphism
  by_contra hBad
  apply hNoCopy
  refine ⟨Z, P, hP, e, ⟨hWeak, ?_⟩⟩
  intro U E hIrred h
  by_contra hNoTargetEmbed
  have hNoSourceLift :
      ¬ ∃ k : Structure.Embedding E w.source,
        ∀ x : U, q (k x) = e (h x) := by
    rintro ⟨k, hk⟩
    obtain ⟨out, hout⟩ := w.homEmbedding.2 E hIrred k
    apply hNoTargetEmbed
    refine ⟨out, ?_⟩
    intro x
    calc
      out x = w.toTarget (k x) := hout x
      _ = (q (k x)).1 := rfl
      _ = (e (h x)).1 := congrArg Subtype.val (hk x)
  exact hBad ⟨Z, P, hP, e, U, E, hIrred, h,
    hNoTargetEmbed, hNoSourceLift⟩


/-- The exact unconditional structural split available from the
printed image-closure axiom at a GLOBAL support minimizer.

Either one transportable forbidden copy supplies an ACTUAL
injective global support-minimal EHN witness, or some support-
minimal original weak witness has a forbidden full quotient
copy containing a specific nonliftable irreducible test with
no matching full embedding into the ambient target.

No global injectivization is assumed. The second alternative
is a concrete missing geometric datum, not a proof admission.
This is the strongest source-matched reduction currently known
without the extra maximal-common-lift root hypotheses. -/
theorem minimalForbiddenEHNWitness_injectiveOr_badIrreducibleWeakImageTest
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    (∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly) ∨
    (∃ w : ForbiddenEHNWitness F Target,
      (∀ v : ForbiddenEHNWitness F Target,
        w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly) ∧
      HasForbiddenWeakImageBadIrreducibleTest F Target w) := by
  obtain ⟨w, hMin⟩ :=
    exists_minimalForbiddenEHNWitness_support
      F Target AOnly hExists
  by_cases hCopy : HasTransportableForbiddenWeakImageCopy F Target w
  · left
    obtain ⟨v, hInj, hCount⟩ :=
      forbiddenWeakImage_injectiveReplacement_of_existsTransportableCopy
        F hFiniteF Target AOnly w hCopy
    refine ⟨v, hInj, ?_⟩
    intro w'
    exact hCount.trans (hMin w')
  · right
    exact ⟨w, hMin,
      forbiddenWeakImage_existsBadIrreducibleTest_of_noTransportableCopy
        F hImage Target w hCopy⟩

end AllThoseRamseyClasses.Lifts

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure

/-- The genuine C5/T failure of even existential weak-image
transport yields an actual forbidden full quotient-copy and an
irreducible source test witnessing failed FULL target reflection
as well as failed lifting into the original C5 source.

This is the concrete local obstruction to the formerly assumed
weak-image/full-target correspondence, not a counterexample
to maximal-lift strong amalgamation. -/
theorem fiveCycle_hasBadForbiddenWeakImageIrreducibleTest :
    HasForbiddenWeakImageBadIrreducibleTest
      fiveCycleImageFamily triangleExtraTernary
      cycle5ForbiddenEHNWitness :=
  forbiddenWeakImage_existsBadIrreducibleTest_of_noTransportableCopy
    fiveCycleImageFamily fiveCycleImageFamily_printedImageClosed
    triangleExtraTernary cycle5ForbiddenEHNWitness
    fiveCycle_weakImage_noTransportableForbiddenCopy

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
