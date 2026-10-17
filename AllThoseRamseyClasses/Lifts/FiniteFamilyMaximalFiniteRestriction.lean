import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalWitnessExistence

/-!
# Root restriction and genuine FINITE maximal-witness existence

Two elementary but important missing links for the finite-family
all-closed-component homogenization:

* A witness maximal along the full embedded old root X stays maximal
  along EVERY further full rooted substructure Y ↪ X. This is the
  hereditary side of the intended maximal lifted age, and does not
  assert that canonical lifts themselves are hereditary.
* When K is explicitly the FINITE forbidden-free structures, finite
  profile maximization really selects a FINITE maximal witness. The
  unqualified K=Forb(F) theorem does not alone supply finiteness of
  the selected carrier.

These lemmas do not assert the hereditary/AP/Ramsey class theorem:
a class of lifted traces and full embedding transport must still be
assembled, and the original 2019 arbitrary regular-family case is
not part of this finite-index alternative.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Maximal canonical-tag profiles can be restricted to any smaller
FULL old functional root without loss. The statement concerns
maximality of observations in an ambient witness, not realization
inside the smaller root's own canonical lift. -/
theorem FiniteNamedCanonicalMaximalAlong.restrict_root
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (K : ∀ {W : Type}, Structure L W → Prop)
    {UY UX UA : Type}
    {Y : Structure L UY} {X : Structure L UX}
    {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (iY : Structure.Embedding Y X)
    (hMax : FiniteNamedCanonicalMaximalAlong Family K iA) :
    FiniteNamedCanonicalMaximalAlong Family K (iA.comp iY) := by
  intro UC C hC e tag xs
  have h := hMax C hC e tag (iY ∘ xs)
  simpa only [Function.comp_assoc] using h

/-- The exact class of FINITE native structures avoiding all
weak EHN embeddings of a finite named forbidden family. -/
def FiniteNamedFiniteForbiddenFree
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {W : Type} (A : Structure L W) : Prop :=
  Finite W ∧ AvoidsFiniteNamedEHN Family A

/-- The finite-family profile maximization theorem can be
specialized so that both the original A and the resulting maximal
witness B are FINITE native functional structures. No AP/JEP,
local finiteness, or finite bound on the size of B is assumed.

Maximality is among FINITE forbidden-free full extensions; it is
not silently promoted to maximality against arbitrary infinite
extensions. -/
theorem finiteNamed_exists_finite_maximal_extension
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UX UA : Type} [Fintype UX] [Finite UA]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hAvoidA : AvoidsFiniteNamedEHN Family A) :
    ∃ (UB : Type) (B : Structure L UB),
      Finite UB ∧ AvoidsFiniteNamedEHN Family B ∧
      ∃ (e : Structure.Embedding A B),
        FiniteNamedCanonicalMaximalAlong Family
          (fun {W : Type} (C : Structure L W) =>
            FiniteNamedFiniteForbiddenFree Family C)
          (e.comp iA) := by
  obtain ⟨UB, B, ⟨hFinite, hAvoid⟩, e, hMax⟩ :=
    finiteNamed_exists_maximal_extension Family
      (fun {W : Type} (C : Structure L W) =>
        FiniteNamedFiniteForbiddenFree Family C)
      iA ⟨inferInstance, hAvoidA⟩
  exact ⟨UB, B, hFinite, hAvoid, e, hMax⟩

end AllThoseRamseyClasses.Lifts
