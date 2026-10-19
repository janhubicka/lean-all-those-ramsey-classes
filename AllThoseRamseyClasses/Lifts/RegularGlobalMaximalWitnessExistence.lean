import AllThoseRamseyClasses.Lifts.MaximalGlobalLiftAlong
import AllThoseRamseyClasses.Lifts.RegularLiftPrecompactness
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Maximal witnesses for the original regular global functional-piece lift

For the original 2019 DISTINCT-root canonical lift, the global
piece-class signature may be infinite, but regularity makes each
positive arity fibre finite. On a fixed finite OLD root X, an added
relation can be positive only at an injective root tuple. Therefore
the complete space of *potentially positive observations* on X is
finite, even for an arbitrary regular infinite forbidden family.

An actual old full embedding monotonically preserves positive
canonical piece observations. Choosing a K-allowed extension which
maximizes the finite set of observations on X yields a witness whose
entire canonical global relation profile on X cannot grow further.

The resulting theorem constructs a genuine maximal witness ALONG X;
it does not assume or imply strong amalgamation or Ramsey. In
particular it does not repair the printed minimal-separator Claim 2
or turn weak root maps into injective ones. It works for any supplied
class K and needs no AP or JEP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A finite index for all root observations which CAN be true on a
fixed finite carrier: an arity between 1 and |X|, a global genuine
piece class at that width, and an ordered root tuple. The tuple is
not required to be injective here; positivity will enforce that. -/
abbrev RegularGlobalRootObservation
    (F : ∀ {W : Type}, Structure L W → Prop)
    (UX : Type) [Fintype UX] :=
  Σ k : {j : Fin (Fintype.card UX + 1) // 0 < j.1},
    GlobalFunctionalPieceClass F k.1.1 ×
      (Fin k.1.1 → UX)

/-- Regularity makes the set of all POTENTIALLY positive
global-piece relation queries on any finite old root finite.
No globally finite relation signature or uniform arity bound is
assumed. -/
theorem regularGlobalRootObservation_finite
    (F : ∀ {W : Type}, Structure L W → Prop)
    (UX : Type) [Fintype UX]
    (hRegular : GlobalFunctionalPieceRegular F) :
    Finite (RegularGlobalRootObservation F UX) := by
  letI (k : {j : Fin (Fintype.card UX + 1) // 0 < j.1}) :
      Finite (GlobalFunctionalPieceClass F k.1.1) :=
    hRegular k.1.1 k.2
  infer_instance

/-- Recover the actual globally indexed piece-class relation
corresponding to a bounded-width observation. -/
def regularGlobalRootObservationSymbol
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX : Type} [Fintype UX]
    (p : RegularGlobalRootObservation F UX) :
    GlobalFunctionalPieceSymbol F :=
  ⟨⟨p.1.1.1, p.1.2⟩, p.2.1⟩

/-- The ordered old-root arguments for one bounded observation. -/
def regularGlobalRootObservationTuple
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX : Type} [Fintype UX]
    (p : RegularGlobalRootObservation F UX) :
    Fin (globalFunctionalPieceArity F
      (regularGlobalRootObservationSymbol F p)) → UX :=
  p.2.2

/-- The finite full positive canonical profile induced on a fixed
root X through a full old embedding iA into a witness A. -/
noncomputable def regularGlobalRootProfile
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Finset (RegularGlobalRootObservation F UX) := by
  classical
  letI : Finite (RegularGlobalRootObservation F UX) :=
    regularGlobalRootObservation_finite F UX hRegular
  letI : Fintype (RegularGlobalRootObservation F UX) :=
    Fintype.ofFinite _
  exact Finset.univ.filter (fun p =>
    (globalFunctionalCanonicalLift F A).rel
      (.inr (regularGlobalRootObservationSymbol F p))
      (iA ∘ regularGlobalRootObservationTuple F p))

/-- Profile membership is EXACTLY the canonical relation of its
associated genuine global-piece symbol at the embedded root tuple. -/
theorem regularGlobalRootProfile_mem
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (p : RegularGlobalRootObservation F UX) :
    p ∈ regularGlobalRootProfile F hRegular iA ↔
    (globalFunctionalCanonicalLift F A).rel
      (.inr (regularGlobalRootObservationSymbol F p))
      (iA ∘ regularGlobalRootObservationTuple F p) := by
  classical
  simp [regularGlobalRootProfile]

/-- Every original-language FULL embedding preserves positive
canonical global-piece relations. Reflection does not hold without
maximality, and no source-root collision is overlooked. -/
theorem globalCanonicalRelation_map_fullEmbedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (s : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F s) → UA)
    (h : (globalFunctionalCanonicalLift F A).rel
      (.inr s) xs) :
    (globalFunctionalCanonicalLift F B).rel
      (.inr s) (e ∘ xs) := by
  change functionalCanonicalExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F)
    A s xs at h
  change functionalCanonicalExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F)
    B s (e ∘ xs)
  exact functionalCanonicalExtraBig_map_embedding L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F)
    e s xs h

/-- The entire finite set of positive root observations only grows
under an old-language FULL embedding of canonical witnesses. -/
theorem regularGlobalRootProfile_mono
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {UX UA UB : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    {B : Structure L UB}
    (iA : Structure.Embedding X A)
    (e : Structure.Embedding A B) :
    regularGlobalRootProfile F hRegular iA ⊆
      regularGlobalRootProfile F hRegular (e.comp iA) := by
  intro p hp
  have hA :=
    (regularGlobalRootProfile_mem F hRegular iA p).mp hp
  have hB :=
    globalCanonicalRelation_map_fullEmbedding F e
      (regularGlobalRootObservationSymbol F p)
      (iA ∘ regularGlobalRootObservationTuple F p) hA
  exact (regularGlobalRootProfile_mem F hRegular
    (e.comp iA) p).mpr hB

/-- ACTUAL maximal witness for the original regular
root-injective canonical lift. Every K-allowed A containing a
finite old root X has a K-allowed full extension B whose induced
canonical global-piece profile on X is preserved by all further
K-allowed extensions.

K may restrict extensions to finite structures, making the
produced B finite when membership in K implies finite carrier.
No strong amalgamation, JEP, source injectivization, or
Ramsey theorem is used. -/
theorem regularGlobal_exists_maximal_extension
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    {UX UA : Type} [Fintype UX]
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hA : K A) :
    ∃ (UB : Type) (B : Structure L UB),
      K B ∧ ∃ (e : Structure.Embedding A B),
        GlobalCanonicalMaximalAlong F K (e.comp iA) := by
  classical
  let Obs := RegularGlobalRootObservation F UX
  letI : Finite Obs :=
    regularGlobalRootObservation_finite F UX hRegular
  letI : Finite (Finset Obs) := inferInstance
  let possible : Set (Finset Obs) :=
    {P | ∃ (UB : Type) (B : Structure L UB),
      K B ∧ ∃ (e : Structure.Embedding A B),
        regularGlobalRootProfile F hRegular (e.comp iA) = P}
  letI : Fintype (Finset Obs) := Fintype.ofFinite _
  let candidates : Finset (Finset Obs) :=
    Finset.univ.filter (fun Q => Q ∈ possible)
  have hNonempty : candidates.Nonempty := by
    refine ⟨regularGlobalRootProfile F hRegular iA, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      ⟨UA, A, hA, Structure.Embedding.id A, rfl⟩⟩
  obtain ⟨P, hP, hBest⟩ :=
    Finset.exists_max_image candidates
      (fun Q : Finset Obs => Q.card) hNonempty
  have hPpossible : P ∈ possible := (Finset.mem_filter.mp hP).2
  obtain ⟨UB, B, hB, e, hEq⟩ := hPpossible
  refine ⟨UB, B, hB, e, ?_⟩
  intro UC C hC eBC s xs
  constructor
  · intro hRelC
    have hinjC : Function.Injective
        (eBC ∘ (e.comp iA) ∘ xs) :=
      globalFunctionalCanonicalRelation_injective
        F C s (eBC ∘ (e.comp iA) ∘ xs) hRelC
    have hinjX : Function.Injective xs := by
      intro j k hjk
      apply hinjC
      exact congrArg
        (fun z : UX => eBC (e (iA z))) hjk
    let m : ℕ := Fintype.card UX
    have hle : globalFunctionalPieceArity F s ≤ m := by
      simpa only [Fintype.card_fin, m] using
        (Fintype.card_le_of_injective xs hinjX)
    let k : {j : Fin (m + 1) // 0 < j.1} :=
      ⟨⟨globalFunctionalPieceArity F s,
          Nat.lt_succ_of_le hle⟩,
        globalFunctionalPieceArity_positive F s⟩
    let p : Obs := ⟨k, (s.2, xs)⟩
    have hSymbol :
        regularGlobalRootObservationSymbol F p = s := by
      rcases s with ⟨⟨n, hn⟩, cls⟩
      rfl
    have hTuple :
        regularGlobalRootObservationTuple F p = xs := rfl
    have hExtended :
        regularGlobalRootProfile F hRegular
          ((eBC.comp e).comp iA) ∈ possible := by
      exact ⟨UC, C, hC, eBC.comp e, rfl⟩
    have hCard :
        (regularGlobalRootProfile F hRegular
          ((eBC.comp e).comp iA)).card ≤
        (regularGlobalRootProfile F hRegular
          (e.comp iA)).card := by
      calc
        _ ≤ P.card := hBest _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hExtended⟩)
        _ = _ := by rw [hEq]
    have hMono :
        regularGlobalRootProfile F hRegular (e.comp iA) ⊆
        regularGlobalRootProfile F hRegular
          ((eBC.comp e).comp iA) :=
      regularGlobalRootProfile_mono F hRegular (e.comp iA) eBC
    have hProfileEq := Finset.eq_of_subset_of_card_le hMono hCard
    have hMemberC :
        p ∈ regularGlobalRootProfile F hRegular
          ((eBC.comp e).comp iA) := by
      apply (regularGlobalRootProfile_mem F hRegular
        ((eBC.comp e).comp iA) p).2
      rcases s with ⟨⟨n, hn⟩, cls⟩
      exact hRelC
    have hMemberB :
        p ∈ regularGlobalRootProfile F hRegular
          (e.comp iA) := by
      rw [hProfileEq]
      exact hMemberC
    have hRelB :=
      (regularGlobalRootProfile_mem F hRegular
        (e.comp iA) p).mp hMemberB
    rcases s with ⟨⟨n, hn⟩, cls⟩
    exact hRelB
  · intro hRelB
    exact globalCanonicalRelation_map_fullEmbedding
      F eBC s ((e.comp iA) ∘ xs) hRelB

end AllThoseRamseyClasses.Lifts
