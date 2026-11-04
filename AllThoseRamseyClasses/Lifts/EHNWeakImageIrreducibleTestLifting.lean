import AllThoseRamseyClasses.Lifts.EHNWeakImageForbiddenLocalTransport

/-!
# Track D: source-test lifting is sufficient for weak-image EHN transport

The printed tuple-surjective image closure yields a forbidden FULL
substructure P of the SOURCE-generated weak image Q of a forbidden
weak witness f : Source → Target. The inclusion Q → Target is only
weak, so a forbidden P may fail to transport as an EHN map.

Here is a more structural, SOURCE-SIDE sufficient condition:
EVERY full irreducible test E of every forbidden embedded P in Q
can be lifted to a full embedding E → Source whose image in Q has
EXACTLY the prescribed coordinates.

Then the original EHN map f provides a FULL target embedding of E
with those same coordinates, while the positive P → Target map
comes from the weak inclusion of Q. Hence P → Target is EHN.
The support-preserving injective replacement theorem from
EHNWeakImageForbiddenLocalTransport is available.

The hypothesis is intentionally NOT claimed automatic.
In the C5/T example, the generated quotient has a forbidden
triangle that does not have a full triangle lift to the original
C5 source. The gap is source test-lifting, not global positive
preservation. The actual maximal-common-lift geometry might
imply a restricted lifting criterion or require a different flip.

No unrestricted strong AP, Claim 2, or injectivization theorem is
claimed in this file.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An irreducible test in a full forbidden substructure of the
source-generated weak quotient lifts to a FULL irreducible source
test with exactly the prescribed quotient coordinates.

This is a source-geometry condition; it does NOT assert full
reflection of the entire weak quotient in Target. -/
def ForbiddenWeakImageIrreducibleTestsLift
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target) : Prop :=
  ∀ {Z : Type} (P : Structure L Z),
    F P →
    ∀ (e : Structure.Embedding P
      (Structure.weakImage w.source Target w.toTarget)),
      ∀ {U : Type} (E : Structure L U),
        E.Irreducible →
        ∀ (h : Structure.Embedding E P),
          ∃ g : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (g x) = e (h x)

/-- The original EHN witness makes *every* lifted source test into
a full target test. Together with weak positive incidence
preservation of the generated image, this proves the exact
forbidden-piece local transport required in Track D. -/
theorem forbiddenWeakImage_localTransport_of_irreducibleTestLifting
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UT : Type} (Target : Structure L UT)
    (w : ForbiddenEHNWitness F Target)
    (hLift : ForbiddenWeakImageIrreducibleTestsLift F Target w) :
    ForbiddenFullWeakImagePiecesTransport F Target w := by
  intro Z P hP e
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  have hInclude : Q.IsWeakHomomorphism Target Subtype.val :=
    Structure.weakImage.inclusion_weak w.homEmbedding.1
  constructor
  · exact hInclude.comp e.isWeakHomomorphism
  · intro U E hIrred h
    obtain ⟨g, hg⟩ := hLift P hP e E hIrred h
    obtain ⟨out, hout⟩ := w.homEmbedding.2 E hIrred g
    refine ⟨out, ?_⟩
    intro x
    calc
      out x = w.toTarget (g x) := hout x
      _ = (Structure.weakImage.quotientMap
        (f := w.toTarget) (g x)).1 := rfl
      _ = (e (h x)).1 := congrArg Subtype.val (hg x)

/-- Paper-shaped forbidden-family image closure and irreducible
SOURCE-test lifting jointly yield an actual injective forbidden
target witness of no greater original A-only SOURCE support.

The source-test lifting assumption remains explicit and is NOT
obtained from regularity or the common maximal-lift hypotheses. -/
theorem forbiddenWeakImage_injectiveReplacement_of_sourceTestLifting
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hLift : ForbiddenWeakImageIrreducibleTestsLift F Target w) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  exact forbiddenWeakImage_injectiveReplacement_of_localTransport
    F hFiniteF hImage Target AOnly w
    (forbiddenWeakImage_localTransport_of_irreducibleTestLifting
      F Target w hLift)

/-- Conditional source-support minimizer under the purely
SOURCE/weak-image test-lifting condition for each forbidden
witness, without assuming a full induced target image or an
induced-range relation-tuple coverage hypothesis. -/
theorem exists_injectiveMinimalForbiddenEHNWitness_of_sourceTestLifting
    (F : ∀ {X : Type}, Structure L X → Prop)
    (hFiniteF : ∀ {X : Type} (Src : Structure L X),
      F Src → Finite X)
    (hImage : HasTupleSurjectiveForbiddenImageClosure F)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (hLift : ∀ w : ForbiddenEHNWitness F Target,
      ForbiddenWeakImageIrreducibleTestsLift F Target w)
    (hExists : Nonempty (ForbiddenEHNWitness F Target)) :
    ∃ v : ForbiddenEHNWitness F Target,
      Function.Injective v.toTarget ∧
      ∀ w : ForbiddenEHNWitness F Target,
        v.sourceSupportCount AOnly ≤ w.sourceSupportCount AOnly := by
  exact exists_injectiveMinimalForbiddenEHNWitness_of_weakImageLocalTransport
    F hFiniteF hImage Target AOnly
    (fun w =>
      forbiddenWeakImage_localTransport_of_irreducibleTestLifting
        F Target w (hLift w))
    hExists

end AllThoseRamseyClasses.Lifts
