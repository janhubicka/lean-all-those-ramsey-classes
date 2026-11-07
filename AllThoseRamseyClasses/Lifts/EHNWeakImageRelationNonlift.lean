import AllThoseRamseyClasses.Lifts.EHNWeakImageFullFunctionFibre

/-!
# Track D: the remaining extra target relation is not a lifted source incidence

The source-generated quotient Q consists EXACTLY of positive
source relation/function incidences on the actual quotient
coordinates. Let E embed FULLY into Q, and suppose E has no
positive relation tuple at some arguments. Then NO positive
source relation tuple can have those quotient coordinates:
otherwise it would generate the missing relation tuple in Q
and reflect through the FULL E -> Q embedding.

This is independent of any EHN/finite/root hypothesis. The
subsequent Track D application uses the already conditional
source function-input coverage theorem to eliminate native
function-fibre surplus and isolate an actual side relation tuple.

Thus that side relation is not just missing from E: there is
no positive original forbidden-source tuple anywhere in the
preimage fibres with the prescribed target coordinates.
The original Section 3 maximal-lift proof must use its
canonical rooted profiles to exclude such a target-only tuple
(or bypass the issue with a collision-tolerant flip).

The input-test coverage hypothesis does NOT follow automatically
from printed regularity. No global strong amalgamation claim.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A missing relation tuple of any FULL substructure of the
source-generated quotient has NO positive original-source
tuple lifting exactly its quotient coordinates.

The quotient is not assumed to embed fully in Target. -/
theorem weakImageFullTest_missingRelation_noSourcePositiveLift
    {V W U : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → U)
    (hMissing : ¬ E.rel R xs)
    (ys : Fin (L.relArity R) → V)
    (hCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    ¬ A.rel R ys := by
  intro hSource
  have hQuotient :
      (Structure.weakImage A B f).rel R (e ∘ xs) := by
    change ∃ (args : Fin (L.relArity R) → V),
      A.rel R args ∧
      ∀ i, (e ∘ xs) i =
        (⟨f (args i), ⟨args i, rfl⟩⟩ : Set.range f)
    exact ⟨ys, hSource, fun i => Subtype.ext (hCoords i).symm⟩
  exact hMissing ((e.map_rel_iff R xs).mp hQuotient)

/-- The same source-incidence obstruction may be witnessed by
a target-only relation tuple in an ACTUAL full side. The
coordinate map is only assumed to agree after composing with
the full side embedding. -/
theorem weakImageFullTest_sideExtraRelation_noSourcePositiveLift
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hSideCoords : ∀ x, j (g x) = (e x).1)
    (R : L.RelSymbol)
    (xs : Fin (L.relArity R) → U)
    (hMissing : ¬ E.rel R xs)
    (ys : Fin (L.relArity R) → V)
    (hCoords : ∀ i, f (ys i) = j (g (xs i))) :
    ¬ A.rel R ys := by
  exact weakImageFullTest_missingRelation_noSourcePositiveLift
    A B f E e R xs hMissing ys
    (fun i => (hCoords i).trans (hSideCoords (xs i)))

/-- With full source irreducible input-test coverage, the
global bad-test certificate in a genuine free amalgam must
include a source-UNLIFTABLE positive target relation tuple,
not merely an unexplained failure of full reflection.

The original forbidden EHN map may be noninjective, but
the chosen full quotient test has injective target coordinates.
All source functions remain native and set-valued. -/
theorem badForbiddenWeakImageTest_hasUnliftableSideRelation_of_inputTests
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UX UA UB UT : Type}
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (w : ForbiddenEHNWitness F Target)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests w.source)
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
    ∃ (Z : Type) (P : Structure L Z),
      F P ∧
      ∃ (e : Structure.Embedding P
        (Structure.weakImage w.source Target w.toTarget))
        (U : Type) (E : Structure L U),
        E.Irreducible ∧
        ∃ (h : Structure.Embedding E P),
          (¬ ∃ k : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∃ (g : U → UA),
             E.IsWeakHomomorphism Left g ∧
             (∀ x : U, jL (g x) = (e (h x)).1) ∧
             ∃ (R : L.RelSymbol)
               (xs : Fin (L.relArity R) → U),
               Left.rel R (g ∘ xs) ∧
               ¬ E.rel R xs ∧
               ∀ ys : Fin (L.relArity R) → w.Carrier,
                 (∀ i, w.toTarget (ys i) = jL (g (xs i))) →
                 ¬ w.source.rel R ys) ∨
           (∃ (g : U → UB),
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             ∃ (R : L.RelSymbol)
               (xs : Fin (L.relArity R) → U),
               Right.rel R (g ∘ xs) ∧
               ¬ E.rel R xs ∧
               ∀ ys : Fin (L.relArity R) → w.Carrier,
                 (∀ i, w.toTarget (ys i) = jR (g (xs i))) →
                 ¬ w.source.rel R ys)) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, hSide⟩ :=
    badForbiddenWeakImageTest_hasSideExtraRelation_of_sourceInputTests
      F Root Left Right Target sL sR jL jR hFree w hCover hBad
  refine ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, ?_⟩
  rcases hSide with ⟨g, hg, hCoords, R, xs, hRel, hMissing⟩ |
      ⟨g, hg, hCoords, R, xs, hRel, hMissing⟩
  · left
    refine ⟨g, hg, hCoords, R, xs, hRel, hMissing, ?_⟩
    intro ys hYs
    exact weakImageFullTest_sideExtraRelation_noSourcePositiveLift
      w.source Target w.toTarget E (e.comp h)
      Left jL g hCoords R xs hMissing ys hYs
  · right
    refine ⟨g, hg, hCoords, R, xs, hRel, hMissing, ?_⟩
    intro ys hYs
    exact weakImageFullTest_sideExtraRelation_noSourcePositiveLift
      w.source Target w.toTarget E (e.comp h)
      Right jR g hCoords R xs hMissing ys hYs

end AllThoseRamseyClasses.Lifts
