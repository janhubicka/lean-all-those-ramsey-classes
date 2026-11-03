import AllThoseRamseyClasses.Lifts.FiniteFamilyShadowFreeAmalgamation
import PartiteConstruction.Functional.AmbientRelativeWeakFunctions
import Mathlib.Data.Fintype.Card

/-!
# Track E2: the CORRECT exact weak-test locality for finite forbidden families

A literal weak restriction to S may delete some values of an ambient
set-valued function. Thus a full irreducible structure of the truncated
weak restriction need NOT be a full substructure of the ambient C.
Requiring an ordinary EHN completion of every weak restriction is in
general TOO STRONG, and cannot serve as the arbitrary-function
2019 Ramsey-picture invariant.

The verified functional partite library supplies the appropriate
notion IsAmbientRelativeWeakHE C S W g instead:
* preserve every positive weak relation and function incidence;
* preserve a COMPLETE nonempty ambient function fibre when every
  output of that input lies in the literal weak vertex set S;
* protect exactly those FULL irreducible native substructures of C
  whose images happen to lie in S, not spurious irreducibles made
  possible only by deleting outside function outputs.

We prove an exact finite-family local-to-global characterization.
If every original weak subset S of a finite native structure D of
size at most n has a finite forbidden-free AMBIENT-RELATIVE completion,
then D itself avoids the entire finite named EHN forbidden family,
provided n bounds every forbidden source's carrier size.

Crucially the converse also holds: if D is finite and forbidden-free,
then its literal weak inclusion S -> D is an ambient-relative
completion for EVERY weak S. This fails for the stronger ordinary
EHN-completion predicate, and explains why the weaker ambient-relative
notion is the correct E2 target.

No closure hull, guessed image injection, domain reflection of
undefined inputs, or singleton-valuedness is used. This theorem
does not construct a sparse Ramsey control or its protected
marked Bbar-copies; it certifies the precise locality obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The literal weak inclusion of ANY vertex subset S into its
native ambient structure is an ambient-relative weak EHN map.
Only actual full ambient irreducible tests are protected.

This does NOT say that weak inclusion is an ordinary EHN map:
truncating an ambient function fibre can create artificial
irreducible tests. -/
theorem ambientRelativeWeakHE_inclusion
    {VD : Type} (D : Structure L VD) (S : Set VD) :
    IsAmbientRelativeWeakHE D S D (fun x : S => x.1) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro R xs hx
    exact hx
  · intro F xs y hy
    exact hy
  · intro F xs _hNonempty hAll
    change imageSet Subtype.val ((D.weakInduce S).func F xs) =
      D.func F (Subtype.val ∘ xs)
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y, hAll y hy⟩, hy, rfl⟩
  · intro X E _hE e _he
    exact ⟨e, fun _ => rfl⟩

/-- The genuine ambient-relative EHN completion condition at an
explicit finite test cutoff n. S is the EXACT original weak
vertex subset, not its function closure. The target W is finite
and genuinely forbidden-free, and the local map is only
ambient-relative weak, not a full map of the entire D. -/
def FiniteNamedAmbientRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} (D : Structure L VD) (n : ℕ) : Prop :=
  ∀ (S : Set VD), Nat.card S ≤ n →
    ∃ (VW : Type) (W : Structure L VW),
      Finite VW ∧ AvoidsFiniteNamedEHN Family W ∧
      ∃ (g : S → VW),
        IsAmbientRelativeWeakHE D S W g

/-- A forbidden EHN map whose image is contained in S composes
with an ambient-relative weak completion of S. The irreducible-test
proof uses the ORIGINAL ambient full embedding of each test,
not the possibly clipped weak substructure.

Thus no false negative function-fibre reflection is required
on a weak test. -/
theorem ehnHomomorphismEmbedding_comp_ambientRelativeWeakHE
    {UA VD VW : Type}
    {A : Structure L UA} {D : Structure L VD}
    {W : Structure L VW}
    {f : UA → VD}
    (hf : A.IsEHNHomomorphismEmbedding D f)
    (S : Set VD) (hRange : ∀ x : UA, f x ∈ S)
    (g : S → VW)
    (hg : IsAmbientRelativeWeakHE D S W g) :
    A.IsEHNHomomorphismEmbedding W
      (g ∘ fun x : UA => (⟨f x, hRange x⟩ : S)) := by
  let fS : UA → S := fun x => ⟨f x, hRange x⟩
  change A.IsEHNHomomorphismEmbedding W (g ∘ fS)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs hx
    have hS : (D.weakInduce S).rel R (fS ∘ xs) :=
      hf.1.1 R xs hx
    exact hg.1.1.1 R (fS ∘ xs) hS
  · intro F xs y hy
    have hS : fS y ∈ (D.weakInduce S).func F (fS ∘ xs) :=
      hf.1.2 F xs y hy
    exact hg.1.1.2 F (fS ∘ xs) (fS y) hS
  · intro X E hE e
    obtain ⟨eD, hED⟩ := hf.2 E hE e
    have heS : ∀ x, eD x ∈ S := by
      intro x
      rw [hED x]
      exact hRange (e x)
    obtain ⟨eW, hEW⟩ := hg.2 E hE eD heS
    refine ⟨eW, ?_⟩
    intro x
    calc
      eW x = g ⟨eD x, heS x⟩ := hEW x
      _ = g (fS (e x)) := by
        congr 1
        apply Subtype.ext
        exact hED x

/-- If n dominates every finite forbidden source cardinality,
ambient-relative weak completions of all exact weak vertex tests
of size <= n force GLOBAL EHN forbidden-source avoidance.

Proof: take the literal image S of a supposed forbidden map.
S has at most as many vertices as the named source, and every
genuine irreducible source test survives in the ambient D.
The ambient-relative completion composes with the original EHN
map to contradict forbidden avoidance in its finite target. -/
theorem avoidsFiniteNamedEHN_of_ambientRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] (D : Structure L VD)
    (n : ℕ)
    (hBound : ∀ i : Family.Index,
      Nat.card (Family.Carrier i) ≤ n)
    (hLocal : FiniteNamedAmbientRelativeWeakCompletions
      Family D n) :
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
  letI : Finite (Family.Carrier i) := Family.finiteCarrier i
  letI : Fintype (Family.Carrier i) := Fintype.ofFinite _
  letI : Finite S := inferInstance
  letI : Fintype S := Fintype.ofFinite _
  have hCard : Nat.card S ≤ Nat.card (Family.Carrier i) := by
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_surjective fS hSurj)
  obtain ⟨VW, W, _hFinW, hAvoidW, g, hg⟩ :=
    hLocal S (hCard.trans (hBound i))
  have hComp :
      (Family.source i).IsEHNHomomorphismEmbedding W (g ∘ fS) :=
    ehnHomomorphismEmbedding_comp_ambientRelativeWeakHE
      hf S (fun x => ⟨x, rfl⟩) g hg
  exact (hAvoidW i (g ∘ fS)) hComp

/-- Every finite forbidden-free native structure has ambient-relative
weak completions of all its literal weak subsets at EVERY cutoff,
simply by using its original full ambient structure as target.
The inclusion is ambient-relative, not ordinary EHN. -/
theorem ambientRelativeWeakCompletions_of_avoidsFiniteNamedEHN
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] (D : Structure L VD)
    (hAvoid : AvoidsFiniteNamedEHN Family D)
    (n : ℕ) :
    FiniteNamedAmbientRelativeWeakCompletions Family D n := by
  intro S _hSize
  exact ⟨VD, D, inferInstance, hAvoid, Subtype.val,
    ambientRelativeWeakHE_inclusion D S⟩

/-- EXACT finite-family locality for genuine partial/set-valued
functions under ambient-relative weak completion semantics.
For any cutoff n covering all finite forbidden sources, GLOBAL
avoidance is equivalent to completion of every original weak
subset of size <= n by a finite forbidden-free structure.

Unlike ordinary EHN completions of clipped weak substructures,
this equivalence is valid even when functions have outputs
outside tested weak subsets. -/
theorem avoidsFiniteNamedEHN_iff_ambientRelativeWeakCompletions
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VD : Type} [Finite VD] (D : Structure L VD)
    (n : ℕ)
    (hBound : ∀ i : Family.Index,
      Nat.card (Family.Carrier i) ≤ n) :
    AvoidsFiniteNamedEHN Family D ↔
      FiniteNamedAmbientRelativeWeakCompletions Family D n := by
  constructor
  · intro hAvoid
    exact ambientRelativeWeakCompletions_of_avoidsFiniteNamedEHN
      Family D hAvoid n
  · intro hLocal
    exact avoidsFiniteNamedEHN_of_ambientRelativeWeakCompletions
      Family D n hBound hLocal

end AllThoseRamseyClasses.Lifts
