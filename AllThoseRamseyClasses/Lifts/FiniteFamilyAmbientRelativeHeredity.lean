import AllThoseRamseyClasses.Lifts.FiniteFamilyAmbientRelativeLocality
import Mathlib.Data.Fintype.Card

/-!
# Track E2: ambient-relative weak tests pull back through FULL embeddings

The correct finite-family local-completion predicate is relative to
a specific ambient functional structure, not the clipped weak
structure treated as an isolated source. It protects complete
function fibres on input tuples whose actual ambient fibres are
entirely inside the test S, and only genuinely embedded full
ambient irreducibles lying within S.

We show this completion invariant is HEREDITARY under arbitrary
FULL original functional embeddings C -> D. Given a literal weak
vertex set S of C, use the literal image e[S] in D, without
taking a generated function-closure hull. The full embedding
identifies the complete ambient fibres over those inputs:
  D.F(e(x)) = e[C.F(x)].
Hence a fibre contained in S is mapped onto the full D-fibre,
which lies within e[S]; the ambient-relative completion of
the weak test e[S] transfers to S.

Full ambient irreducible substructures are protected by
composition with the original FULL embedding. No spurious
irreducible of the clipped weak restriction is introduced.
Surjectivity S -> e[S] gives the required cardinal bound.

This yields a bona fide monotone input lemma for the E2
partite construction, independent of the forbidden family and
of the not-yet-constructed sparse Ramsey picture.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite full embedding preserves the correct ambient-relative
weak completion property when the exact test S is pulled back
from the exact vertex image e[S]. In particular all complete
nonempty set-valued function fibres on protected tests agree,
and only actual ambient irreducibles are protected. -/
theorem ambientRelativeWeakHE_pullback_fullEmbedding
    {UC UD UW : Type}
    {C : Structure L UC} {D : Structure L UD}
    {W : Structure L UW}
    (e : Structure.Embedding C D)
    (S : Set UC)
    (g : (e '' S) → UW)
    (hg : IsAmbientRelativeWeakHE D (e '' S) W g) :
    IsAmbientRelativeWeakHE C S W
      (g ∘ fun x : S =>
        (⟨e x.1, ⟨x.1, x.2, rfl⟩⟩ : e '' S)) := by
  let T : Set UD := e '' S
  let j : S → T :=
    fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  change IsAmbientRelativeWeakHE C S W (g ∘ j)
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro R xs hx
    have hd : (D.weakInduce T).rel R (j ∘ xs) :=
      (e.map_rel_iff R (Subtype.val ∘ xs)).mpr hx
    exact hg.1.1.1 R (j ∘ xs) hd
  · intro F xs y hy
    have hNative : e y.1 ∈
        D.func F (e ∘ (Subtype.val ∘ xs)) := by
      rw [← e.map_func F (Subtype.val ∘ xs)]
      exact ⟨y.1, hy, rfl⟩
    have hd : j y ∈ (D.weakInduce T).func F (j ∘ xs) :=
      hNative
    exact hg.1.1.2 F (j ∘ xs) (j y) hd
  · intro F xs hNonempty hAll
    have hNonD :
        (D.func F (e ∘ (Subtype.val ∘ xs))).Nonempty := by
      obtain ⟨y, hy⟩ := hNonempty
      refine ⟨e y, ?_⟩
      rw [← e.map_func F (Subtype.val ∘ xs)]
      exact ⟨y, hy, rfl⟩
    have hAllD :
        ∀ y, y ∈ D.func F (e ∘ (Subtype.val ∘ xs)) →
          y ∈ T := by
      intro y hy
      rw [← e.map_func F (Subtype.val ∘ xs)] at hy
      obtain ⟨z, hz, hyz⟩ := hy
      exact ⟨z, hAll z hz, hyz⟩
    have hD := hg.1.2 F (j ∘ xs) hNonD hAllD
    change imageSet (g ∘ j)
        ((C.weakInduce S).func F xs) =
      W.func F ((g ∘ j) ∘ xs)
    calc
      imageSet (g ∘ j) ((C.weakInduce S).func F xs) =
        imageSet g ((D.weakInduce T).func F (j ∘ xs)) := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨j y, hy, rfl⟩
        · rintro ⟨y, hy, rfl⟩
          have hNative :
              y.1 ∈ D.func F (e ∘ (Subtype.val ∘ xs)) := hy
          rw [← e.map_func F (Subtype.val ∘ xs)] at hNative
          obtain ⟨w, hw, hEq⟩ := hNative
          have hwS : w ∈ S := hAll w hw
          let wS : S := ⟨w, hwS⟩
          have hInside : j wS = y := by
            apply Subtype.ext
            exact hEq
          exact ⟨wS, hw, congrArg g hInside⟩
      _ = W.func F ((g ∘ j) ∘ xs) := hD
  · intro X E hE r hr
    let rD : Structure.Embedding E D := e.comp r
    have hrD : ∀ x, rD x ∈ T := by
      intro x
      exact ⟨r x, hr x, rfl⟩
    obtain ⟨rW, hrW⟩ := hg.2 E hE rD hrD
    refine ⟨rW, ?_⟩
    intro x
    calc
      rW x = g ⟨rD x, hrD x⟩ := hrW x
      _ = (g ∘ j) ⟨r x, hr x⟩ := rfl

/-- Genuine finite-family ambient-relative weak local completion
is inherited along an arbitrary FULL native embedding. The
source-size cutoff is unchanged, because the literal test image
e[S] has no more vertices than S.

No function closure is taken; this works with nullary functions,
all arities and complete set-valued output fibres. -/
theorem finiteNamedAmbientRelativeWeakCompletions_of_embedding
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {UC UD : Type} [Finite UC] [Finite UD]
    {C : Structure L UC} {D : Structure L UD}
    (e : Structure.Embedding C D)
    (n : ℕ)
    (hD : FiniteNamedAmbientRelativeWeakCompletions Family D n) :
    FiniteNamedAmbientRelativeWeakCompletions Family C n := by
  intro S hSize
  let T : Set UD := e '' S
  let j : S → T := fun x =>
    ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
  have hSurj : Function.Surjective j := by
    intro x
    rcases x.2 with ⟨y, hy, hEq⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hEq
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Fintype T := Fintype.ofFinite T
  have hCard : Nat.card T ≤ Nat.card S := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective j hSurj)
  obtain ⟨UW, W, hFiniteW, hAvoidW, g, hg⟩ :=
    hD T (hCard.trans hSize)
  exact ⟨UW, W, hFiniteW, hAvoidW, g ∘ j,
    ambientRelativeWeakHE_pullback_fullEmbedding e S g hg⟩

end AllThoseRamseyClasses.Lifts
