import AllThoseRamseyClasses.Published.LiteralDeletedOutputBound
import AllThoseRamseyClasses.Published.MinimalRepair4b
import AllThoseRamseyClasses.Published.FinitePairedClass
import Mathlib.Tactic

/-!
# Even corrected 2019 (4b) bounds every candidate by |C0|+1

IMPORTANT: This analysis retains ORIGINAL 2019 U-completions.
The proposed one-clause correction to (4b) excludes only
U-CLOSED U-irreducible tests.

In a U-closed structure C satisfying this corrected membership
antecedent, an induced singleton C|{x} cannot itself be U-closed:
otherwise it would have to belong to K, which has no singletons.

The exact closedness/U-substructure equivalence therefore produces
an actual matching closure tuple rooted at x and escaping {x}.
The literal 2019 map into C0 must embed C minus the escaped output.
The verified deleted-output result then yields a nearly-full-source
injection into C0 and a size bound.

This may show the proposed (4b)-only correction does NOT repair
the first main theorem. It does not assert class strong amalgamation,
nor silently change Definition 2.15.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- In the corrected (4b) hypothesis every singleton MUST be a weak
nonclosed substructure: it is intrinsically irreducible but cannot
be a member of the paired class. -/
theorem corrected_cover_singleton_not_closed
    {V : Type} (C : RelStructure Lang V)
    (hCover : CorrectedUIrreduciblesIn finitePairedClass mateRules C)
    (x : V) :
    ¬ IsUClosed mateRules (C.induce {x}) := by
  intro hSingleton
  have hMem : finitePairedClass (C.induce {x}) :=
    hCover {x} hSingleton (singleton_isUIrreducible mateRules C x)
  letI : Nonempty ({x} : Set V) := ⟨⟨x, Set.mem_singleton x⟩⟩
  letI : Subsingleton ({x} : Set V) := ⟨by
    intro a b
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.2).trans
      (Set.mem_singleton_iff.mp b.2).symm⟩
  exact no_singleton_member (C.induce {x}) hMem.2

/-- Every vertex of a corrected-cover U-closed candidate forces a
genuine matching closure tuple with an output outside the root.
The embedding e and its root coordinates are those of the ORIGINAL
2019 closure-description rule. -/
theorem corrected_cover_has_escaping_output
    {V : Type} (C : RelStructure Lang V)
    (hClosed : IsUClosed mateRules C)
    (hCover : CorrectedUIrreduciblesIn finitePairedClass mateRules C)
    (x : V) :
    ∃ (e : Embedding mateRoot C)
      (t : Fin (Lang.arity mateRule.symbol) → V),
      C.rel mateRule.symbol t ∧
      (∀ k : Fin mateRule.rootSize,
        t (k.castLE mateRule.rootLE) = e k) ∧
      ∃ (j : Fin (Lang.arity mateRule.symbol)),
        ∀ k : Fin mateRule.rootSize, t j ≠ e k := by
  classical
  have hBad : ¬ IsUSubstructure mateRules C {x} := by
    intro hS
    exact (corrected_cover_singleton_not_closed C hCover x)
      (hClosed.induce_of_USubstructure {x} hS)
  unfold IsUSubstructure at hBad
  push_neg at hBad
  obtain ⟨rule, hrule, t, ht, hRoot, j, hOutside⟩ := hBad
  have hRule : rule = mateRule := by
    simpa only [mateRules, Set.mem_singleton_iff] using hrule
  subst rule
  obtain ⟨e, he⟩ := (hClosed mateRule (by simp [mateRules])).1 t ht
  refine ⟨e, t, ht, he, j, ?_⟩
  intro k hEq
  have hInsideRoot : e k ∈ ({x} : Set V) := by
    rw [← he k]
    exact hRoot k
  have hInsideOutput : t j ∈ ({x} : Set V) := by
    simpa [hEq] using hInsideRoot
  exact hOutside hInsideOutput

/-- An embedding of all but one vertex into P gives an injection
of ALL vertices into Option P (send the missing output to none). -/
theorem injective_option_of_deleted_embedding
    {V P : Type} (q : V)
    (g : deletedOutputSet q → P)
    (hg : Function.Injective g) :
    ∃ f : V → Option P, Function.Injective f := by
  classical
  let f : V → Option P := fun x =>
    if hx : x = q then none else some (g ⟨x, hx⟩)
  refine ⟨f, ?_⟩
  intro x y hxy
  by_cases hx : x = q
  · by_cases hy : y = q
    · exact hx.trans hy.symm
    · have hBad : (none : Option P) = some (g ⟨y, hy⟩) := by
        simpa [f, hx, hy] using hxy
      cases hBad
  · by_cases hy : y = q
    · have hBad : some (g ⟨x, hx⟩) = (none : Option P) := by
        simpa [f, hx, hy] using hxy
      cases hBad
    · have heq : g ⟨x, hx⟩ = g ⟨y, hy⟩ := by
        have hs : some (g ⟨x, hx⟩) = some (g ⟨y, hy⟩) := by
          simpa [f, hx, hy] using hxy
        exact Option.some.inj hs
      exact congrArg Subtype.val (hg heq)

/-- The finite cardinal inequality derived from an Option P
injection, without any assumption that P is nonempty. -/
theorem card_le_succ_of_option_injective
    {V P : Type} [Finite V] [Finite P]
    (f : V → Option P) (hf : Function.Injective f) :
    Nat.card V ≤ Nat.card P + 1 := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  have hCard : Nat.card V ≤ Nat.card (Option P) :=
    Nat.card_le_card_of_injective f hf
  simpa [Nat.card_eq_fintype_card] using hCard

/-- Even the CORRECTED (4b) antecedent, together with the ORIGINAL
2019 (4a) completion map, forces C to have at most |C0|+1
vertices for the paired matching closure rule. -/
theorem corrected_cover_literal_control_card_bound
    {V P : Type} [Finite V] [Finite P]
    (C : RelStructure Lang V) (C0 : RelStructure Lang P)
    (hClosed : IsUClosed mateRules C)
    (hCover : CorrectedUIrreduciblesIn finitePairedClass mateRules C)
    (hControl : IsUCompletion mateRules C C0) :
    Nat.card V ≤ Nat.card P + 1 := by
  classical
  by_cases hNonempty : Nonempty V
  · obtain ⟨x⟩ := hNonempty
    obtain ⟨e, t, ht, hRoot, j, hGenuine⟩ :=
      corrected_cover_has_escaping_output C hClosed hCover x
    obtain ⟨f, hf⟩ := hControl.2
    obtain ⟨g, _⟩ :=
      literalMap_embeds_deleted_output hClosed mateRule
        (by simp [mateRules]) e t ⟨ht, hRoot⟩ j hGenuine f hf
    obtain ⟨opt, hInj⟩ :=
      injective_option_of_deleted_embedding (t j) g g.injective
    exact card_le_succ_of_option_injective opt hInj
  · let f : V → Option P := fun _ => none
    have hInj : Function.Injective f := by
      intro x y _
      exact (hNonempty ⟨x⟩).elim
    exact card_le_succ_of_option_injective f hInj

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
