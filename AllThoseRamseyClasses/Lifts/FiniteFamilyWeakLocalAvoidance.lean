import AllThoseRamseyClasses.Lifts.FiniteFamilyShadowFreeAmalgamation
import PartiteConstruction.Functional.OriginalPartialWeakImage

/-!
# Track E: finite forbidden families detected on EXACT weak images

In the finite named forbidden-family setting, the remaining Ramsey
construction needs to turn locally completable weak tests into a
single globally forbidden-free native picture.

A weak EHN forbidden-source map F -> D has an image carried by at
most |F| vertices. Its range need NOT be function-closed: a native
partial/set-valued function on a tuple in the image can have additional
outputs outside the image. Thus the correct small target is the
EXACT WEAK induced substructure D.weakInduce (range f), not the
closure hull or an allegedly full induced substructure.

We show that an EHN map remains EHN upon restricting the target to
ANY weak subset containing its full vertex image. For irreducible
tests, full embeddings restrict to the weak target using the genuine
full-fibre codomain restriction lemma. Then, if each weak subset
dominated in cardinality by a source of the finite named family has
an EHN completion in some forbidden-free native structure, a
forbidden EHN map into D would compose with the completion and
contradict avoidance.

This is the exact finite-size/local-to-global avoidance inference.
It does NOT construct those small completions, the preceding sparse
partite picture, or the common maximizing witness diagrams needed
to preserve B-copies. No original 2019 root injectivity is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- EHN maps can restrict their codomain to any EXACT weak vertex
subset containing the map image. Neither the set nor the image is
assumed closed under the target functions.

Protected irreducible full source tests remain full in the weak
target, since every actual complete output fibre of an embedded
test is already in its own embedded image. -/
theorem ehnHomomorphismEmbedding_codRestrictWeak
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    {f : UA → UB}
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (S : Set UB)
    (hRange : ∀ x : UA, f x ∈ S) :
    A.IsEHNHomomorphismEmbedding (B.weakInduce S)
      (fun x : UA => (⟨f x, hRange x⟩ : S)) := by
  let fS : UA → S := fun x => ⟨f x, hRange x⟩
  change A.IsEHNHomomorphismEmbedding (B.weakInduce S) fS
  constructor
  · constructor
    · intro R xs hx
      simpa only [Structure.weakInduce_rel, Function.comp_def, fS]
        using hf.1.1 R xs hx
    · intro F xs y hy
      simpa only [Structure.weakInduce_func, Function.comp_def, fS]
        using hf.1.2 F xs y hy
  · intro X E hE e
    obtain ⟨g, hg⟩ := hf.2 E hE e
    have hG : ∀ x : X, g x ∈ S := by
      intro x
      rw [hg x]
      exact hRange (e x)
    exact ⟨g.codRestrictWeak S hG, by
      intro x
      apply Subtype.ext
      exact hg x⟩

/-- Genuine local forbidden-family completion criterion on the
literal weak induced vertex sets S of a native candidate D.

The bound is stated WITHOUT choosing a maximum source size:
S must admit a surjection from the carrier of some particular
forbidden source. For finite carriers this is equivalent to
|S| <= |F_i|, including empty and colliding source images.

Unlike a global full embedding, the local EHN map may be
noninjective; the complete original weak test is retained.
The completion target is an ACTUAL finite forbidden-free structure,
not a merely hypothetical class label. -/
def FiniteNamedWeakSmallCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} (D : Structure L VD) : Prop :=
  ∀ (i : Family.Index) (S : Set VD),
    (∃ (e : Family.Carrier i → S), Function.Surjective e) →
    ∃ (VW : Type) (W : Structure L VW),
      Finite VW ∧ AvoidsFiniteNamedEHN Family W ∧
      ∃ (g : S → VW),
        (D.weakInduce S).IsEHNHomomorphismEmbedding W g

/-- Local-to-global avoidance for a finite named EHN forbidden
family. Every forbidden source witness has an EXACT weak image
among the small tests, even if the image is not function-closed.

This proves an E2 LOCALITY step with no extra image-injectivity,
source connectedness or free-amalgamation hypothesis. It does
not assert the existence of the local completions themselves. -/
theorem avoidsFiniteNamedEHN_of_weakSmallCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} (D : Structure L VD)
    (hLocal : FiniteNamedWeakSmallCompletions Family D) :
    AvoidsFiniteNamedEHN Family D := by
  intro i f hf
  let S : Set VD := Set.range f
  let fS : Family.Carrier i → S :=
    fun x => ⟨f x, ⟨x, rfl⟩⟩
  have hSurj : Function.Surjective fS := by
    intro s
    obtain ⟨x, hx⟩ := s.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  obtain ⟨VW, W, _, hAvoidW, g, hg⟩ :=
    hLocal i S ⟨fS, hSurj⟩
  have hSmall :
      (Family.source i).IsEHNHomomorphismEmbedding
        (D.weakInduce S) fS :=
    ehnHomomorphismEmbedding_codRestrictWeak hf S
      (by intro x; exact ⟨x, rfl⟩)
  exact (hAvoidW i (g ∘ fS)) (hg.comp hSmall)

end AllThoseRamseyClasses.Lifts
