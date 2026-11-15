import AllThoseRamseyClasses.Lifts.Claim2SelectedQAactiveSourceIncrease

/-!
# Exact A-source neutrality iff inserted selected-Q nonroots are A-free

The strict A-support increase barrier can be completed to an exact
characterization for a genuine native selected-Q replacement of an
OLD A-free selected component. Full original A-support lies in
the old complete complement E; the new source is Q +_R E, with
unchanged E weak-map target coordinates.

If ALL new Q nonroot vertices are A-inactive, EVERY NEW A-active
source vertex also lies in the NEW E-image. Exact native full
embeddings transport the SAME A-active E-source subtype to old
and new sources, so their total A-source Nat.card is IDENTICAL.

Conversely, if any new Q nonroot maps A-exclusive, the previous
checked strict-increase theorem gives strictly larger NEW support,
so equality is impossible.

This is a real SOURCE-cardinality equivalence, not weak image
counting. It identifies the exact A-neutrality certificate needed
before the proposed B-descent can remain in the class of global
A-minimizing forbidden weak-map witnesses.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Exact old/new total A-active SOURCE-cardinality equality
from common full retained complement E, exact E target-map
agreement, and the fact that ALL A-active source vertices
in BOTH old and new sources belong to their respective E images.
No weak-map injectivity is required. -/
theorem fullNativeRetainedComplement_Aactive_card_eq
    {V W E UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L E}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hOldAllAInE : ∀ v : V, f v ∈ AActive →
      v ∈ Set.range iOldE)
    (hNewAllAInE : ∀ w : W, flip w ∈ AActive →
      w ∈ Set.range iNewE)
    (hEAgree : ∀ e : E, flip (iNewE e) = f (iOldE e)) :
    Nat.card {v : V // f v ∈ AActive} =
      Nat.card {w : W // flip w ∈ AActive} := by
  classical
  let S : Set E := {e | f (iOldE e) ∈ AActive}
  have hOldEq : {v : V | f v ∈ AActive} = iOldE '' S := by
    ext v
    constructor
    · intro hv
      change f v ∈ AActive at hv
      obtain ⟨e, he⟩ := hOldAllAInE v hv
      refine ⟨e, ?_, he⟩
      change f (iOldE e) ∈ AActive
      simpa only [he] using hv
    · rintro ⟨e, heA, rfl⟩
      exact heA
  have hNewEq : {w : W | flip w ∈ AActive} = iNewE '' S := by
    ext w
    constructor
    · intro hw
      change flip w ∈ AActive at hw
      obtain ⟨e, he⟩ := hNewAllAInE w hw
      refine ⟨e, ?_, he⟩
      change f (iOldE e) ∈ AActive
      have h : flip (iNewE e) ∈ AActive := by
        simpa only [he] using hw
      rwa [hEAgree e] at h
    · rintro ⟨e, heA, rfl⟩
      change flip (iNewE e) ∈ AActive
      rw [hEAgree e]
      exact heA
  have hOldCard :
      Nat.card {v : V // f v ∈ AActive} =
        Nat.card {e : E // e ∈ S} := by
    change Nat.card (↑({v : V | f v ∈ AActive} : Set V)) =
      Nat.card (↑(S : Set E))
    rw [hOldEq]
    exact Nat.card_image_of_injective iOldE.injective _
  have hNewCard :
      Nat.card {w : W // flip w ∈ AActive} =
        Nat.card {e : E // e ∈ S} := by
    change Nat.card (↑({w : W | flip w ∈ AActive} : Set W)) =
      Nat.card (↑(S : Set E))
    rw [hNewEq]
    exact Nat.card_image_of_injective iNewE.injective _
  exact hOldCard.trans hNewCard.symm

/-- In an actual geometric selected-Q replacement, if the
original inner nonroot component contains no A-active SOURCE
vertex and EVERY inserted Q-nonroot SOURCE vertex is A-inactive,
then the old and new TOTAL A-active SOURCE counts are exactly
equal. Q-root vertices lie in the full retained E-image
by the genuine source free-amalgam overlap. -/
theorem geometricSelectedQ_nonrootAfree_preserves_totalASourceCount
    {V W UT : Type}
    (Old : Structure L V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ AActive)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hQNonrootNoA : ∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
      flip (iQ q) ∉ AActive) :
    Nat.card {v : V // f v ∈ AActive} =
      Nat.card {w : W // flip w ∈ AActive} := by
  let iOldE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range inner.roots) inner.minimal.1 inner.left
  have hOldAllAInE : ∀ v : V, f v ∈ AActive →
      v ∈ Set.range iOldE := by
    intro v hvA
    have hvNotInner : v ∉ functionalComponentFrom Old
        (Set.range inner.roots) inner.left := by
      intro hvInner
      exact hOldInnerNoA v hvInner hvA
    exact ⟨⟨v, hvNotInner⟩, rfl⟩
  have hNewAllAInE : ∀ w : W, flip w ∈ AActive →
      w ∈ Set.range iE := by
    intro w hwA
    rcases hNewFree.covers w with ⟨q, hqw⟩ | ⟨e, hew⟩
    · by_cases hqRoot : q ∈ Set.range Q.rootEmbedding
      · obtain ⟨r, hr⟩ := hqRoot
        have hOverlap :
            iQ (Q.rootEmbedding r) =
              iE ((geometricGlobalComplementChart Old inner).rootEmbedding r) :=
          (hNewFree.overlap _ _).mpr ⟨r, rfl, rfl⟩
        refine ⟨(geometricGlobalComplementChart Old inner).rootEmbedding r, ?_⟩
        calc
          iE ((geometricGlobalComplementChart Old inner).rootEmbedding r)
              = iQ (Q.rootEmbedding r) := hOverlap.symm
          _ = iQ q := congrArg iQ hr
          _ = w := hqw.symm
      · have hqA : flip (iQ q) ∈ AActive := by
          simpa only [hqw] using hwA
        exact False.elim ((hQNonrootNoA q hqRoot) hqA)
    · exact ⟨e, hew.symm⟩
  exact fullNativeRetainedComplement_Aactive_card_eq
    iOldE iE f flip AActive
    hOldAllAInE hNewAllAInE hEAgree

/-- In an actual finite selected-Q replacement of an OLD A-free
inner component, exact global A-active SOURCE neutrality is
EQUIVALENT to every inserted Q-nonroot SOURCE vertex being
A-inactive.

This is the precise necessary-and-sufficient condition for
preservation of total A-source rank through the flip.
It does NOT prove an eligible A-neutral canonical selected Q
exists at every positive B-rank state. -/
theorem geometricSelectedQ_totalASourceNeutral_iff_nonrootAfree
    {V W UT : Type}
    (Old : Structure L V) (hFiniteOld : Finite V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W) (hFiniteNew : Finite W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ AActive)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1) :
    (Nat.card {v : V // f v ∈ AActive} =
      Nat.card {w : W // flip w ∈ AActive}) ↔
    (∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
        flip (iQ q) ∉ AActive) := by
  constructor
  · intro hEq q hqNonroot
    exact geometricSelectedQ_nonIncreasingA_forces_nonroot_Afree
      Old hFiniteOld inner Q New hFiniteNew
      iQ iE hNewFree f flip AActive hOldInnerNoA hEAgree
      hEq.symm.le q hqNonroot
  · intro hNoQNonrootA
    exact geometricSelectedQ_nonrootAfree_preserves_totalASourceCount
      Old inner Q New iQ iE hNewFree
      f flip AActive hOldInnerNoA hEAgree hNoQNonrootA

/-- Conditional preservation of the ORIGINAL global A-source
support minimum by one genuine native selected-Q flip.

If the removed old selected component is A-free and the
inserted Q-nonroot source vertices are ALSO A-free, the
exact source-cardinality equality above proves that the
new forbidden weak target-map witness has the SAME global
A-support minimality property as the old witness.

This is a logical transfer interface. It does NOT assert that
such an A-neutral canonical replacement Q can be selected
at every positive B-source rank. -/
theorem geometricSelectedQ_nonrootAfree_preserves_globalAMinimum
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type}
    (Old : Structure L V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (hNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (Target : Structure L UT)
    (f : V → UT) (flip : W → UT) (AActive : Set UT)
    (hFlip : New.IsEHNHomomorphismEmbedding Target flip)
    (hOldInnerNoA : ∀ z : V,
      z ∈ functionalComponentFrom Old
        (Set.range inner.roots) inner.left → f z ∉ AActive)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1)
    (hQNonrootNoA : ∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
        flip (iQ q) ∉ AActive)
    (hOldAMinimum : ∀ {Z : Type}
      (Candidate : Structure L Z) (hCandidate : F Candidate)
      (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {v : V // f v ∈ AActive} ≤
        Nat.card {z : Z // g z ∈ AActive}) :
    F New ∧
    New.IsEHNHomomorphismEmbedding Target flip ∧
    (∀ {Z : Type}
      (Candidate : Structure L Z) (hCandidate : F Candidate)
      (g : Z → UT),
      Candidate.IsEHNHomomorphismEmbedding Target g →
      Nat.card {w : W // flip w ∈ AActive} ≤
        Nat.card {z : Z // g z ∈ AActive}) := by
  have hEqual :
      Nat.card {v : V // f v ∈ AActive} =
        Nat.card {w : W // flip w ∈ AActive} :=
    geometricSelectedQ_nonrootAfree_preserves_totalASourceCount
      Old inner Q New iQ iE hNewFree
      f flip AActive hOldInnerNoA hEAgree hQNonrootNoA
  refine ⟨hNew, hFlip, ?_⟩
  intro Z Candidate hCandidate g hg
  calc
    Nat.card {w : W // flip w ∈ AActive} =
      Nat.card {v : V // f v ∈ AActive} := hEqual.symm
    _ ≤ Nat.card {z : Z // g z ∈ AActive} :=
      hOldAMinimum Candidate hCandidate g hg

end AllThoseRamseyClasses.Lifts
