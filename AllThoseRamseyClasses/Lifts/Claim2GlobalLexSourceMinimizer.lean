import AllThoseRamseyClasses.Lifts.Claim2ZeroBTerminalSourceFlip
import Mathlib.Data.Set.Card

/-!
# Choosing a global source-support minimizing weak forbidden witness

Several verified 2019 Claim 2 sublemmas take as an explicit premise
a finite F-forbidden ORIGINAL source with a weak EHN target map
that globally minimizes the number of SOURCE vertices sent to
the A-exclusive target region, among ALL forbidden sources/weak
maps into the same fixed free amalgam.

This source-witness minimizer exists WITHOUT NORMALIZING the map
to be injective. The set of eligible natural-number SOURCE counts
is nonempty when any forbidden weak-map witness exists, and
the least element is attained by an actual eligible witness.

One can simultaneously break ties by minimizing B-exclusive
SOURCE support among all those globally A-minimal witnesses.
The lexicographic minimizer is also attained by one actual
finite forbidden structure and one true weak EHN target map.

These are selection lemmas, NOT an initial mixed-piece existence
theorem and NOT a proof that a B→A replacement remains in this
globally A-minimal class. No target-image cardinality is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every nonempty family of finite F-forbidden native SOURCE
witnesses weakly mapping to the SAME target has a REAL member
minimizing the total number of source vertices mapped into
a fixed target set Active.

The weak map need NOT be injective; hFiniteF ensures the cost
is a genuine finite SOURCE cardinality rather than an infinite
Nat.card default. The choice ranges over ALL eligible finite
F-source/map pairs, not over target images. -/
theorem exists_global_minimum_weakForbiddenSource_support
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UT : Type}
    (Target : Structure L UT)
    (Old : Structure L V) (hOld : F Old)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (Active : Set UT) :
    ∃ (W : Type) (New : Structure L W) (hNew : F New)
      (hFiniteNew : Finite W) (g : W → UT)
      (hg : New.IsEHNHomomorphismEmbedding Target g),
      ∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (k : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target k →
        Nat.card {w : W // g w ∈ Active} ≤
          Nat.card {z : Z // k z ∈ Active} := by
  classical
  let costs : Set ℕ :=
    {n | ∃ (W : Type) (New : Structure L W)
      (hNew : F New) (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g ∧
        Nat.card {w : W // g w ∈ Active} = n}
  have hNonempty : costs.Nonempty := by
    refine ⟨Nat.card {v : V // f v ∈ Active}, ?_⟩
    exact ⟨V, Old, hOld, f, hf, rfl⟩
  have hLeast : sInf costs ∈ costs := Nat.sInf_mem hNonempty
  obtain ⟨W, New, hNew, g, hg, hCost⟩ := hLeast
  refine ⟨W, New, hNew, hFiniteF New hNew, g, hg, ?_⟩
  intro Z Candidate hCandidate k hk
  rw [hCost]
  exact Nat.sInf_le
    (show Nat.card {z : Z // k z ∈ Active} ∈ costs from
      ⟨Z, Candidate, hCandidate, k, hk, rfl⟩)

/-- An ORIGINAL forbidden finite weak-map witness can be
chosen LEXICOGRAPHICALLY minimum in (A-source support,
B-source support), among all such witnesses into the fixed
target. Tie-breaking in B is only among candidates with
the EXACT same globally minimum A-source cardinality.

This choice supplies a legitimate induction/contradiction
starting point but does NOT prove that replacements satisfy
the lexicographic descent hypotheses. -/
theorem exists_global_lex_minimum_weakForbiddenSource_support
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
    {V UT : Type}
    (Target : Structure L UT)
    (Old : Structure L V) (hOld : F Old)
    (f : V → UT)
    (hf : Old.IsEHNHomomorphismEmbedding Target f)
    (AActive BActive : Set UT) :
    ∃ (W : Type) (New : Structure L W) (hNew : F New)
      (hFiniteNew : Finite W) (g : W → UT)
      (hg : New.IsEHNHomomorphismEmbedding Target g),
      (∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (k : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target k →
        Nat.card {w : W // g w ∈ AActive} ≤
          Nat.card {z : Z // k z ∈ AActive}) ∧
      (∀ {Z : Type} (Candidate : Structure L Z)
        (hCandidate : F Candidate) (k : Z → UT),
        Candidate.IsEHNHomomorphismEmbedding Target k →
        Nat.card {z : Z // k z ∈ AActive} =
          Nat.card {w : W // g w ∈ AActive} →
        Nat.card {w : W // g w ∈ BActive} ≤
          Nat.card {z : Z // k z ∈ BActive}) := by
  classical
  obtain ⟨WA, SA, hSA, _hFiniteWA, fA, hfA, hGlobalA⟩ :=
    exists_global_minimum_weakForbiddenSource_support
      F hFiniteF Target Old hOld f hf AActive
  let bestA : ℕ := Nat.card {w : WA // fA w ∈ AActive}
  let bCosts : Set ℕ :=
    {n | ∃ (W : Type) (New : Structure L W)
      (hNew : F New) (g : W → UT),
        New.IsEHNHomomorphismEmbedding Target g ∧
        Nat.card {w : W // g w ∈ AActive} = bestA ∧
        Nat.card {w : W // g w ∈ BActive} = n}
  have hBNonempty : bCosts.Nonempty := by
    refine ⟨Nat.card {w : WA // fA w ∈ BActive}, ?_⟩
    exact ⟨WA, SA, hSA, fA, hfA, rfl, rfl⟩
  have hLeastB : sInf bCosts ∈ bCosts := Nat.sInf_mem hBNonempty
  obtain ⟨W, New, hNew, g, hg, hA, hB⟩ := hLeastB
  refine ⟨W, New, hNew, hFiniteF New hNew, g, hg, ?_, ?_⟩
  · intro Z Candidate hCandidate k hk
    rw [hA]
    exact hGlobalA Candidate hCandidate k hk
  · intro Z Candidate hCandidate k hk hAEqual
    rw [hB]
    exact Nat.sInf_le
      (show Nat.card {z : Z // k z ∈ BActive} ∈ bCosts from
        ⟨Z, Candidate, hCandidate, k, hk, hAEqual.trans hA, rfl⟩)

/-- A lexicographically minimum ORIGINAL forbidden weak-map source
witness cannot admit a new F-forbidden weak-map source with
NONINCREASING global A-exclusive SOURCE cardinality AND
STRICTLY DECREASING global B-exclusive SOURCE cardinality.

The global A-minimality inequality first forces equality of
the A counts; the B tie-breaker then forbids the strict B drop.

This is the exact FINITE-SOURCE contradiction interface for
combining an A-neutral selected-Q successor with the
global B-source descent in the original 2019 Claim 2 proof.
It does NOT assert that such a new witness exists. -/
theorem globalLexMin_avoids_A_nonincrease_and_B_strictDecrease
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type}
    (Target : Structure L UT)
    (Old : Structure L V)
    (f : V → UT)
    (New : Structure L W) (hNew : F New)
    (flip : W → UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (AActive BActive : Set UT)
    (hGlobalAMin : ∀ {Z : Type} (Candidate : Structure L Z)
      (hCandidate : F Candidate) (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V // f v ∈ AActive} ≤
        Nat.card {z : Z // g z ∈ AActive})
    (hBMinAtA : ∀ {Z : Type} (Candidate : Structure L Z)
      (hCandidate : F Candidate) (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {z : Z // g z ∈ AActive} =
        Nat.card {v : V // f v ∈ AActive} →
      Nat.card {v : V // f v ∈ BActive} ≤
        Nat.card {z : Z // g z ∈ BActive})
    (hANonIncreasing :
      Nat.card {w : W // flip w ∈ AActive} ≤
        Nat.card {v : V // f v ∈ AActive})
    (hBStrict :
      Nat.card {w : W // flip w ∈ BActive} <
        Nat.card {v : V // f v ∈ BActive}) : False := by
  have hAEqual :
      Nat.card {w : W // flip w ∈ AActive} =
        Nat.card {v : V // f v ∈ AActive} :=
    Nat.le_antisymm hANonIncreasing
      (hGlobalAMin New hNew flip hFlip)
  exact (Nat.not_lt_of_ge
    (hBMinAtA New hNew flip hFlip hAEqual)) hBStrict

end AllThoseRamseyClasses.Lifts
