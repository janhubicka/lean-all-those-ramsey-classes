import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial
import AllThoseRamseyClasses.Published.InducedClosed2019WeakRankBridge

/-!
# Alternative repaired 2019 Ramsey proof architecture: EXACT WEAK SIZE induction

The 2019 Definition 2.17(4c), unchanged under the proposed coordinated
map/membership repair, requires amended (K,U)-completions of EVERY EXACT
weak induced substructure on at most n vertices. The original
Lemma 2.30 uses the STRONGER invariant that every intrinsically
U-CLOSED substructure of U-generating rank <=n has a K-completion.

Completing only a minimum weak generating set and extending that map
to its prescribed closed hull is FALSE in general (finite adversarial
obstruction documented in merged partite-construction PR #234).
Consequently we must not conclude the stronger original rank
increment merely from weak n-vertex completions.

This file proves a DIFFERENT, paper-faithful conditional endgame:
the fully constructed unrestricted initial Picture and fully
constructed j=0/rank-one Picture provide a finite closed Ramsey
witness with completed ALL weak tests of size <=1.
If genuine native Picture refinements can promote COMPLETABILITY
of all weak exact j-vertex tests to all weak exact (j+1)-vertex
tests for j>=1 while preserving closedness, corrected projection,
closed irreducible K-test coverage and the Ramsey arrow, then the
finite iteration and original local-completion implication prove
the corrected global 2019 Ramsey theorem.

The missing weak-size j->j+1 Picture constructor is an EXPLICIT
hypothesis of the theorem, never an axiom or an invented witness.
It is weaker than proving all closed substructures of generating
rank j+1 completable, and it aligns EXACTLY with the original
quantifiers of clause (4c). It may be approached using maximal
weak-rank decomposition, two ordinary side maps, and a constructed
common A-boundary (separately checked partial results).

No claim is made that the missing native Picture refinement exists.
This alternative conditional endgame does not replace or weaken
the ACTUAL 2019 Definition 2.17 local-completion assumption.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}
variable {UA VB P : Type v}

/-- Concrete finite Ramsey Picture with the ORIGINAL exact weak
induced completion invariant at vertex cutoff n.
Closed rank is not used in this definition. -/
def Has2019WeakSizePictureWitness
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P) (κ : Type*) (n : ℕ) : Prop :=
  ∃ (Z : Type v) (_ : Finite Z) (C : RelStructure L Z),
    IsUClosed rules C ∧
    (∃ f : Z → P,
      IsInducedClosedUHomomorphismEmbedding rules C D f) ∧
    StructuralRamsey.Arrow A B C κ ∧
    CorrectedUIrreduciblesIn K rules C ∧
    (∀ S : Finset Z, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        (C.induce (↑S : Set Z)))

/-- The exact missing WEAK-VERTEX-SIZE increment, without replacing
the tests by closed hulls. A genuine constructor satisfying this
predicate would already be sufficient for the corrected theorem.
It is NOT asserted to exist here. -/
def Proposed2019WeakSizeIncrementStep
    (K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (A : RelStructure L UA) (B : RelStructure L VB)
    (κ : Type*) (j : ℕ) : Prop :=
  ∀ {W : Type v} [Finite W] (D : RelStructure L W),
    IsUClosed rules D →
    StructuralRamsey.Arrow A B D κ →
    CorrectedUIrreduciblesIn K rules D →
    (∀ S : Finset W, S.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (D.induce (↑S : Set W))) →
    Has2019WeakSizePictureWitness K rules A B D κ (j+1)

/-- The true native j=0 Picture construction already gives completed
weak vertex tests of cardinal at most ONE, by the separately verified
closed-hull restriction bridge. This is a CONSTRUCTED base, not the
hypothetical weak-size higher-rank constructor. -/
theorem weakSize2019_actual_base_one
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hBIrred : B.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (hD : IsUClosed rules D)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B D κ) :
    Has2019WeakSizePictureWitness K rules A B D κ 1 := by
  obtain ⟨Z, hZ, C, hCClosed, hProj, hCArrow, hCover, hRankOne⟩ :=
    lemma_2_30_coordinated_rank_zero
      A B D hA hB hKB hBIrred hHer hD κ hArrow
  letI : Finite Z := hZ
  have hAbstractRank : Has2019ClosedRankCompletions K rules C 1 := by
    intro S hFiniteS hClosedS hSizeS
    letI : Fintype S := hFiniteS
    exact (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRankOne S hClosedS hSizeS)
  refine ⟨Z, hZ, C, hCClosed, hProj, hCArrow, hCover, ?_⟩
  exact lemma_2_31_exact_weak_tests_of_closed_rank
    K rules C hCClosed 1 hAbstractRank

/-- Once the WEAK-size increment is provided as an explicit argument,
a finite native Picture tower over ANY closed control D has
completions of every original weak n-vertex test. The rank-one
starting Picture and all projection compositions are genuine. -/
theorem iterate_2019_exact_weak_size_pictures
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (A : RelStructure L UA) (B : RelStructure L VB)
    (D : RelStructure L P)
    [Finite UA] [Finite VB] [Finite P]
    (hA : IsUClosed rules A) (hB : IsUClosed rules B)
    (hKB : K B) (hBIrred : B.Irreducible)
    (hHer : ClosedUHereditary K rules)
    (hD : IsUClosed rules D)
    (κ : Type*) [Fintype κ] [Nonempty κ]
    (hArrow : StructuralRamsey.Arrow A B D κ)
    (hIncrement : ∀ j : ℕ, 1 ≤ j →
      Proposed2019WeakSizeIncrementStep K rules A B κ j)
    (n : ℕ) (hn : 1 ≤ n) :
    Has2019WeakSizePictureWitness K rules A B D κ n := by
  have hAll : ∀ t : ℕ,
      Has2019WeakSizePictureWitness K rules A B D κ (t+1) := by
    intro t
    induction t with
    | zero =>
        exact weakSize2019_actual_base_one
          A B D hA hB hKB hBIrred hHer hD κ hArrow
    | succ t ih =>
        obtain ⟨W, hW, E, hEClosed, ⟨f, hf⟩,
          hEArrow, hECover, hEWeak⟩ := ih
        letI : Finite W := hW
        obtain ⟨Z, hZ, C, hCClosed, ⟨g, hg⟩,
          hCArrow, hCCover, hCWeak⟩ :=
          hIncrement (t+1) (by omega) E
            hEClosed hEArrow hECover hEWeak
        have hComp :
            IsInducedClosedUHomomorphismEmbedding
              rules C D (f ∘ g) :=
          inducedClosedMap_comp_2019 hf hg
        have hWitness :
            Has2019WeakSizePictureWitness K rules A B D κ ((t+1)+1) :=
          ⟨Z, hZ, C, hCClosed, ⟨f ∘ g, hComp⟩,
            hCArrow, hCCover, hCWeak⟩
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hWitness
  have hnEq : n-1+1 = n := Nat.sub_add_cancel hn
  rw [← hnEq]
  exact hAll (n-1)

/-- The corrected 2019 Ramsey theorem follows from only an
EXACT-WEAK-VERTEX-SIZE Picture increment at each j>=1.
The unrestricted initial Picture over potentially NONCLOSED
Ramsey controls and the rank-one base are ACTUALLY CONSTRUCTED.

The fixed cutoff n(B,C0) is selected before building the
Pictures; every exact weak tested vertex set S with |S|<=n
is supplied directly to the original unchanged local (4c).

This is a conditional reduction, NOT an unconditional proof
that the missing weak-size increment exists. -/
theorem coordinated2019_ramsey_of_weaksize_increment
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules)
    (hIncrement :
      ∀ {X Y : Type v} [Finite X] [Finite Y]
        (A : RelStructure L X) (B : RelStructure L Y)
        (κ : Type) [Fintype κ] [Nonempty κ]
        (j : ℕ), 1 ≤ j → K A → K B →
        Proposed2019WeakSizeIncrementStep K rules A B κ j) :
    FiniteRamseyClass K := by
  intro X Y hFX hFY A B hKA hKB κ hFκ hNκ
  have hRA : R A := hK.induced.subset A hKA
  have hRB : R B := hK.induced.subset B hKB
  have hAClosed : IsUClosed rules A := hK.induced.closed A hKA
  have hBClosed : IsUClosed rules B := hK.induced.closed B hKB
  have hBIrred : B.Irreducible := hRIrred B hRB
  have hHer : ClosedUHereditary K rules :=
    embeddedClosedHereditary_of_induced
      hK.induced.hereditary hK.iso
  obtain ⟨Z, hZ, C0, hRC0, hArrow0⟩ :=
    hR A B hRA hRB κ
  letI : Finite Z := hZ
  obtain ⟨n, hLocal⟩ :=
    hK.induced.localCompletion B C0 hKB hRC0
  obtain ⟨W, hW, D, hDClosed, ⟨p0, hp0⟩,
      hDArrow, hDCover⟩ :=
    lemma_2_28_coordinated_unrestricted_induced
      (K := K) (rules := rules)
      A B C0 hAClosed hBClosed hKB hHer κ hArrow0
  letI : Finite W := hW
  have hStep : ∀ j : ℕ, 1 ≤ j →
      Proposed2019WeakSizeIncrementStep K rules A B κ j := by
    intro j hj
    exact hIncrement A B κ j hj hKA hKB
  obtain ⟨T, hT, C, hCClosed, ⟨p1, hp1⟩,
      hCArrow, hCCover, hWeak⟩ :=
    iterate_2019_exact_weak_size_pictures A B D
      hAClosed hBClosed hKB hBIrred hHer hDClosed
      κ hDArrow hStep (n+1) (by omega)
  letI : Finite T := hT
  have hTotalMap :
      IsInducedClosedUHomomorphismEmbedding
        rules C C0 (p0 ∘ p1) :=
    inducedClosedMap_comp_2019 hp0 hp1
  have hCopywise : HasCopywiseCompletion K B C :=
    hLocal C hCClosed
      ⟨hRIrred C0 hRC0, p0 ∘ p1, hTotalMap⟩
      hCCover (fun S hS => hWeak S (by omega))
  exact arrow_of_BCopywiseCompletion_inClass hCArrow hCopywise

end AllThoseRamseyClasses.Published
