import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeLocality
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions
import Mathlib.Data.Fintype.Card

/-!
# Track E2: exact ambient-relative weak completion pulls back along EHN projections

The direct functional partite construction preserves a GLOBAL
EHN homomorphism-embedding projection p : C -> D. Such a
projection is not necessarily injective and is not a globally
FULL homomorphism on undefined function inputs. Hence it is
invalid to treat the weak image of an arbitrary set S as closed
or as the full induced functional substructure of D.

For every literal weak vertex set S of C, consider the literal
image p[S] in D, with no function-closure hull. The already
verified EHN fibre-exactness theorem says that whenever a
source function fibre is NONEMPTY, its image is the entire
target fibre. If the source fibre is also wholly contained in
S, the target fibre is wholly contained in p[S]. The
ambient-relative EHN completion of p[S] therefore composes
with the source projection on S.

Full embeddings of genuine ambient irreducible substructures
inside S are protected by the EHN property of p and by the
ambient-relative completion of p[S]. We never require full
embeddings of spurious irreducibles created by clipped outputs.

Consequently n-bounded ambient-relative weak local completion
passes from D to C along an EHN projection for EVERY n, even
below the forbidden-source size cutoff. This is an actual
small-image inductive invariant for the still missing direct
functional E2 sparsening step, independent of class-level
Ramsey or forbidden-freeness of D.

The construction does not increase n; it does not prove the
mixed-root rank increment from n-1 to n.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Compose a genuine EHN partite projection p:C->D with a
relative weak completion of the EXACT image p[S] of one weak
source test S.

The resulting map on S is ambient-relative:
- every positive old relation/function incidence is preserved;
- every nonempty FULL ambient C fibre lying entirely in S maps
  onto the full W fibre, without output truncation;
- every actual FULL irreducible C substructure contained in S
  maps to a full embedding in W.

No global fibre-surjectivity, domain reflection, S-closedness,
injectivity of p, or closure hull is assumed. -/
theorem ambientRelativeWeakHE_comp_EHNProjection
    {UC UD UW : Type}
    {C : Structure L UC} {D : Structure L UD}
    {W : Structure L UW}
    {p : UC → UD}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (S : Set UC)
    (g : (p '' S) → UW)
    (hg : IsAmbientRelativeWeakHE D (p '' S) W g) :
    IsAmbientRelativeWeakHE C S W
      (g ∘ fun x : S =>
        (⟨p x.1, ⟨x.1, x.2, rfl⟩⟩ : p '' S)) := by
  let T : Set UD := p '' S
  let q : S → T := fun x =>
    ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  change IsAmbientRelativeWeakHE C S W (g ∘ q)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro R xs hx
    have hd : (D.weakInduce T).rel R (q ∘ xs) :=
      hp.1.1 R (Subtype.val ∘ xs) hx
    exact hg.1.1.1 R (q ∘ xs) hd
  · intro F xs y hy
    have hd : q y ∈ (D.weakInduce T).func F (q ∘ xs) :=
      hp.1.2 F (Subtype.val ∘ xs) y.1 hy
    exact hg.1.1.2 F (q ∘ xs) (q y) hd
  · intro F xs hNonempty hAll
    have hFull :
        imageSet p (C.func F (Subtype.val ∘ xs)) =
          D.func F (p ∘ (Subtype.val ∘ xs)) :=
      hp.toOriginalPartial.1.2 F (Subtype.val ∘ xs) hNonempty
    have hNonD :
        (D.func F (p ∘ (Subtype.val ∘ xs))).Nonempty := by
      obtain ⟨z, hz⟩ := hNonempty
      refine ⟨p z, ?_⟩
      rw [← hFull]
      exact ⟨z, hz, rfl⟩
    have hAllD :
        ∀ z, z ∈ D.func F (p ∘ (Subtype.val ∘ xs)) →
          z ∈ T := by
      intro z hz
      rw [← hFull] at hz
      obtain ⟨a, ha, hEq⟩ := hz
      exact ⟨a, hAll a ha, hEq⟩
    have hW := hg.1.2 F (q ∘ xs) hNonD hAllD
    change imageSet (g ∘ q) ((C.weakInduce S).func F xs) =
      W.func F ((g ∘ q) ∘ xs)
    calc
      imageSet (g ∘ q) ((C.weakInduce S).func F xs) =
          imageSet g ((D.weakInduce T).func F (q ∘ xs)) := by
        ext z
        constructor
        · rintro ⟨a, ha, rfl⟩
          have hqa : q a ∈ (D.weakInduce T).func F (q ∘ xs) :=
            hp.1.2 F (Subtype.val ∘ xs) a.1 ha
          exact ⟨q a, hqa, rfl⟩
        · rintro ⟨b, hb, rfl⟩
          have hbD : b.1 ∈ D.func F
              (p ∘ (Subtype.val ∘ xs)) := hb
          rw [← hFull] at hbD
          obtain ⟨a, ha, hEq⟩ := hbD
          have haS : a ∈ S := hAll a ha
          let aS : S := ⟨a, haS⟩
          have hqb : q aS = b := by
            apply Subtype.ext
            exact hEq
          exact ⟨aS, ha, congrArg g hqb⟩
      _ = W.func F ((g ∘ q) ∘ xs) := hW
  · intro X E hE e he
    obtain ⟨eD, heD⟩ := hp.2 E hE e
    have hRange : ∀ x, eD x ∈ T := by
      intro x
      rw [heD x]
      exact ⟨e x, he x, rfl⟩
    obtain ⟨eW, heW⟩ := hg.2 E hE eD hRange
    refine ⟨eW, ?_⟩
    intro x
    calc
      eW x = g ⟨eD x, hRange x⟩ := heW x
      _ = (g ∘ q) ⟨e x, he x⟩ := by
        congr 1
        apply Subtype.ext
        exact heD x

/-- Bounded ambient-relative weak local completion transfers
BACKWARD along a genuine EHN projection C->D, with exactly
the same vertex cutoff n.

The induced map of a test S lands in the literal image p[S].
This image has cardinality <= |S|, even when p identifies
vertices. Thus the existing target test completion transfers
directly, without assuming D avoids the forbidden family or
that S is function-closed. -/
theorem finiteNamedAmbientRelativeWeakCompletions_of_EHNProjection
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UC UD : Type} [Finite UC] [Finite UD]
    {C : Structure L UC} {D : Structure L UD}
    {p : UC → UD}
    (hp : C.IsEHNHomomorphismEmbedding D p)
    (n : ℕ)
    (hD : FiniteNamedAmbientRelativeWeakCompletions Family D n) :
    FiniteNamedAmbientRelativeWeakCompletions Family C n := by
  intro S hSize
  let T : Set UD := p '' S
  let q : S → T := fun x =>
    ⟨p x.1, ⟨x.1, x.2, rfl⟩⟩
  have hSurj : Function.Surjective q := by
    intro x
    obtain ⟨y, hy, hEq⟩ := x.2
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hEq
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype T := Fintype.ofFinite T
  have hCard : Nat.card T ≤ Nat.card S := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective q hSurj)
  obtain ⟨UW, W, hFinW, hAvoidW, g, hg⟩ :=
    hD T (hCard.trans hSize)
  exact ⟨UW, W, hFinW, hAvoidW, g ∘ q,
    ambientRelativeWeakHE_comp_EHNProjection hp S g hg⟩

end AllThoseRamseyClasses.Lifts
