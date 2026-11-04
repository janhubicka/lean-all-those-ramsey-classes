import AllThoseRamseyClasses.Lifts.EHNWeakImageBadIrreducibleTest
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Track D: localize nonliftable irreducible weak-image tests to a full amalgam side

The source-generated weak quotient can contain full forbidden pieces
whose inclusion into the ambient target is not an EHN map.
An irreducible test detecting this failure is a genuine STRUCTURE,
not a bare pair of roots. No global injectivity is assumed.

A short positive statement survives even for arbitrary weak maps
into a genuine FULL native functional free amalgam:
the entire image of an irreducible source test lies in ONE full side.

Instead of rebuilding a large pullback free-decomposition, take the
function-closed hull of the weak image inside the ambient target.
The pinned partite library proves that this hull is irreducible.
Its FULL inclusion into the free amalgam therefore factors into
one of the two sides. In particular this works for arbitrary-arity
partial/set-valued functions and does not require the weak source
map to be injective, EHN, or surjective.

Applying this to a nontransportable full forbidden quotient-copy
makes the obstruction **side-local**: there is a genuine irreducible
test E which maps wholly into one side at the level of VERTICES,
but has NO full embedding into that side with those coordinates.
A full side embedding would compose with its full inclusion to
contradict the already certified failure of target reflection.

This is a useful restriction on the exact missing maximal-lift
geometry, NOT a proof of strong amalgamation or Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Weak maps of actual native irreducible structures into a FULL
free amalgam have their entire vertex images in a single side.

The proof uses the existing closed-hull irreducibility theorem,
not an illicit full embedding of the raw weak image. -/
theorem irreducibleWeakMap_liesInOneFullFreeSide
    {UV UX UA UB UT : Type}
    (E : Structure L UV)
    (hIrr : E.Irreducible)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : UV → UT)
    (hf : E.IsWeakHomomorphism Target f) :
    (∀ x : UV, ∃ a : UA, f x = jL a) ∨
    (∀ x : UV, ∃ b : UB, f x = jR b) := by
  let S : Set UT := Target.functionClosure (Set.range f)
  have hS : Target.IsClosed S :=
    Target.functionClosure_isClosed (Set.range f)
  let Hull : Structure L S := Target.induce S hS
  have hHull : Hull.Irreducible :=
    hIrr.functionClosure_weakImage hf
  let inc : Structure.Embedding Hull Target :=
    Target.inclusion S hS
  rcases hHull hFree inc with hL | hR
  · left
    intro x
    let z : S :=
      ⟨f x, Target.subset_functionClosure
        (Set.range f) ⟨x, rfl⟩⟩
    exact hL z
  · right
    intro x
    let z : S :=
      ⟨f x, Target.subset_functionClosure
        (Set.range f) ⟨x, rfl⟩⟩
    exact hR z

/-- A genuine native irreducible test of ANY full quotient-copy
P ↪ weakImage(w) must have its weak inclusion image contained
in one actual full target side. Importantly, this is only
VERTEX containment: full relation/function reflection remains
a separate obligation. -/
theorem forbiddenWeakImageIrreducibleTest_liesInOneFullFreeSide
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
    {Z : Type} (P : Structure L Z)
    (e : Structure.Embedding P
      (Structure.weakImage w.source Target w.toTarget))
    {U : Type} (E : Structure L U)
    (hIrr : E.Irreducible)
    (h : Structure.Embedding E P) :
    (∀ x : U, ∃ a : UA, (e (h x)).1 = jL a) ∨
    (∀ x : U, ∃ b : UB, (e (h x)).1 = jR b) := by
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  have hWeakQ : E.IsWeakHomomorphism Q (e ∘ h) :=
    (e.comp h).isWeakHomomorphism
  have hWeakTarget : E.IsWeakHomomorphism Target
      (fun x => (e (h x)).1) :=
    (Structure.weakImage.inclusion_weak w.homEmbedding.1).comp
      hWeakQ
  exact irreducibleWeakMap_liesInOneFullFreeSide
    E hIrr Root Left Right Target
    sL sR jL jR hFree
    (fun x => (e (h x)).1) hWeakTarget

/-- The negative alternative in the exact Track D minimizer
dichotomy localizes to ONE actual full amalgam side.
Its irreducible test has no full embedding into that side
with the prescribed weak-image coordinates, despite
its positive vertex image lying entirely inside the side.

This is the precise side-internal reflection obstruction that
an eventual collision-tolerant maximal-lift repair must exclude
or accommodate. No source root-image injectivity is presumed. -/
theorem badForbiddenWeakImageTest_hasSideInternalReflectionFailure
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
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
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
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∀ x : U, ∃ a : UA, (e (h x)).1 = jL a) ∧
            (¬ ∃ g : Structure.Embedding E Left,
              ∀ x : U, jL (g x) = (e (h x)).1) ∨
           (∀ x : U, ∃ b : UB, (e (h x)).1 = jR b) ∧
            (¬ ∃ g : Structure.Embedding E Right,
              ∀ x : U, jR (g x) = (e (h x)).1)) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoTarget, hNoLift⟩ := hBad
  have hSide :=
    forbiddenWeakImageIrreducibleTest_liesInOneFullFreeSide
      F Root Left Right Target sL sR jL jR
      hFree w P e E hIrr h
  refine ⟨Z, P, hP, e, U, E, hIrr, h,
    hNoTarget, hNoLift, ?_⟩
  rcases hSide with hL | hR
  · left
    refine ⟨hL, ?_⟩
    rintro ⟨g, hg⟩
    apply hNoTarget
    exact ⟨jL.comp g, hg⟩
  · right
    refine ⟨hR, ?_⟩
    rintro ⟨g, hg⟩
    apply hNoTarget
    exact ⟨jR.comp g, hg⟩

end AllThoseRamseyClasses.Lifts
