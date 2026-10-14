import AllThoseRamseyClasses.Applications.PosetWeakIrreducibleSeeds
import AllThoseRamseyClasses.Applications.PosetExactWeakCompletion

/-!
# Exact 2019 weak-test K-completions give the pure poset local test

The previous proof of the quasi-cycle theorem used a pure relational
hypothesis hLocal: every ORIGINAL weak finite S with |S|<=|C0|
admits a reflexive transitive partial-order comparison q preserving
old p-edges and reflecting p on every old vertex-order pair in S.

Here we DERIVE exactly that hLocal from the real corrected 2019 (4c):
a finite K-completion of C.induce S with a protected map on every
closed U-irreducible induced substructure. U is EMPTY, so the exact
original 2-point source with an old order edge is irreducible.
The protected map consequently reflects its p nonedges.

Outside the original weak subset S, the pulled-back comparison is
just identity; this keeps reflexivity and transitivity without
assuming the K-completion map injective on ALL of S.

No generated hull or enlarged weak test is used. This closes the
key semantic bridge between the paper's (4c) and the abstract finite
walk argument, but does not itself construct the final global
ordered-poset K-completion.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- From arbitrary weak induced K-completions at the ORIGINAL
cardinal cutoff, derive the exact q_S interface for the path lemma.
Full reflection is demanded only on an old order edge. -/
theorem poset_exact_weak_completions_supply_local_relations
    {V D : Type} [Fintype V] [Fintype D]
    (C : RelStructure Lang V)
    (hReflexive : ∀ x : V, edge C .equiv x x)
    (hSmall : ∀ S : Finset V, S.card ≤ Fintype.card D →
      HasInducedClosedUKCompletion orderedPosetClass
        (∅ : ClosureDescription Lang)
        (C.induce (↑S : Set V))) :
    ∀ S : Finset V, S.card ≤ Fintype.card D →
      ∃ q : V → V → Prop,
        (∀ a : V, q a a) ∧
        (∀ a b c : V, q a b → q b c → q a c) ∧
        (∀ x y, x ∈ S → y ∈ S →
          edge C .equiv x y → q x y) ∧
        (∀ x y, x ∈ S → y ∈ S →
          (x = y ∨ edge C .lt x y) →
          q x y → edge C .equiv x y) := by
  classical
  intro S hS
  obtain ⟨Y, hY, Target, hTarget, _, g, hg⟩ := hSmall S hS
  let I : Set V := ↑S
  let A : RelStructure Lang I := C.induce I
  let q : V → V → Prop := fun x y =>
    x = y ∨ ∃ (hx : x ∈ I) (hy : y ∈ I),
      edge Target .equiv (g ⟨x, hx⟩) (g ⟨y, hy⟩)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro x
    exact Or.inl rfl
  · intro x y z hxy hyz
    rcases hxy with hEq | ⟨hx, hy, hxy⟩
    · subst y
      exact hyz
    rcases hyz with hEq | ⟨hy', hz, hyz⟩
    · subst z
      exact Or.inr ⟨hx, hy, hxy⟩
    · refine Or.inr ⟨hx, hz, ?_⟩
      have hEqI : (⟨y, hy⟩ : I) = ⟨y, hy'⟩ :=
        Subtype.ext rfl
      have hyz' : edge Target .equiv
          (g ⟨y, hy⟩) (g ⟨z, hz⟩) := by
        simpa only [hEqI] using hyz
      exact hTarget.2.2.1 _ _ _ hxy hyz'
  · intro x y hx hy hp
    refine Or.inr ⟨hx, hy, ?_⟩
    have hA : A.rel .equiv ![(⟨x, hx⟩ : I), ⟨y, hy⟩] := by
      change C.rel .equiv ![x, y]
      exact hp
    have hMapped := hg.1 .equiv
      ![(⟨x, hx⟩ : I), ⟨y, hy⟩] hA
    simpa only [Function.comp_def] using hMapped
  · intro x y hx hy hord hq
    rcases hq with hEq | ⟨hx', hy', hMapped⟩
    · subst y
      exact hReflexive x
    rcases hord with heq | hOrder
    · subst y
      exact hReflexive x
    · let sx : I := ⟨x, hx⟩
      let sy : I := ⟨y, hy⟩
      have hOld : edge A .lt sx sy := by
        change C.rel .lt ![x, y]
        exact hOrder
      have hNe : sx ≠ sy := by
        intro h
        have hxy : x = y := congrArg Subtype.val h
        have hAt : edge C .lt x x := by
          simpa [hxy] using hOrder
        have hMappedOrder := hg.1 .lt
          ![(⟨x, hx⟩ : I), ⟨y, hy⟩]
          (show A.rel .lt ![(⟨x, hx⟩ : I), ⟨y, hy⟩] from hOld)
        have hTargetSelf : edge Target .order (g sx) (g sx) := by
          simpa [hxy] using hMappedOrder
        exact hTarget.1.2.1 (g sx) hTargetSelf
      have hPair : (A.induce ({sx, sy} : Set I)).Irreducible :=
        weak_pair_irreducible_of_positive_edge A .lt sx sy hNe hOld
      let pair : Set I := {sx, sy}
      obtain ⟨e, he⟩ := hg.2 pair
        (isUClosed_empty_description _)
        (hPair.isUIrreducible (∅ : ClosureDescription Lang))
      let px : pair := ⟨sx, by simp [pair]⟩
      let py : pair := ⟨sy, by simp [pair]⟩
      have hEqX : e px = g sx := he px
      have hEqY : e py = g sy := he py
      have hMapped' : edge Target .equiv (g sx) (g sy) := by
        have hxEq : (⟨x, hx'⟩ : I) = sx := Subtype.ext rfl
        have hyEq : (⟨y, hy'⟩ : I) = sy := Subtype.ext rfl
        simpa only [hxEq, hyEq] using hMapped
      have hImage : Target.rel .equiv (e ∘ ![px, py]) := by
        change edge Target .equiv (e px) (e py)
        rw [hEqX, hEqY]
        exact hMapped'
      have hSrc : (A.induce pair).rel .equiv ![px, py] :=
        (e.map_rel_iff .equiv ![px, py]).mp hImage
      exact hSrc

end AllThoseRamseyClasses.Applications.OrderedPosets
