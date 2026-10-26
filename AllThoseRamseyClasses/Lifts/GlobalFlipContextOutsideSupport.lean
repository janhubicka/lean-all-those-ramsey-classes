import AllThoseRamseyClasses.Lifts.GlobalFlipOuterContextOutside
import Mathlib.Tactic

/-!
# Outside support is invariant in two native full free-amalgam contexts

Consider two genuine native functional free amalgams over the SAME
full right-hand complement E but possibly different left pieces:
  Old = OldPiece +_Root E,
  New = NewPiece +_Root E.

Fix an arbitrary subset SE of the whole complement E containing
ALL shared-root vertices. Both contexts consist of the entire
respective left piece and exactly the image of SE on the right.

The verified exact outside-context characterization gives a
bijection from E\SE to each outer-context complement. If an old
EHN target map f and a new target map g agree on the unchanged
right complement E, then the SOURCE vertex sets OUTSIDE these
contexts whose target images lie in ANY specified exclusive
target subset B are equivalent, with equal finite cardinality.

This is the missing arithmetic bridge from global to local
support decrease in a contextual Section 3 Claim 2 flip. It
requires no EHN source-map injection. No claim is made about
the minimal-separator or profile status of either context.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Outside-of-context support counts in two genuine full native
free amalgams of different left sides and the SAME right side
are exactly equal when their target maps agree on the right side.

This is equality of cardinalities of ACTUAL source vertices,
not cardinality of distinct target images. -/
theorem fullFreeAmalgam_contextOutside_support_card_eq
    {H OL NL E V W T : Type v}
    [Finite V] [Finite W] [Finite E]
    {Root : Structure L H}
    {OldLeft : Structure L OL}
    {NewLeft : Structure L NL}
    {Right : Structure L E}
    {Old : Structure L V}
    {New : Structure L W}
    {sOldL : Structure.Embedding Root OldLeft}
    {sNewL : Structure.Embedding Root NewLeft}
    {sR : Structure.Embedding Root Right}
    {iOldL : Structure.Embedding OldLeft Old}
    {iOldR : Structure.Embedding Right Old}
    {iNewL : Structure.Embedding NewLeft New}
    {iNewR : Structure.Embedding Right New}
    (hOldFree : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNewFree : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (SE : Set E) (hRootE : ∀ r : H, sR r ∈ SE)
    (f : V → T) (g : W → T) (BOnly : Set T)
    (hSameE : ∀ e : E, g (iNewR e) = f (iOldR e)) :
    Nat.card {w : W //
      w ∉ (iNewL '' (Set.univ : Set NL) ∪ iNewR '' SE) ∧
      g w ∈ BOnly} =
    Nat.card {v : V //
      v ∉ (iOldL '' (Set.univ : Set OL) ∪ iOldR '' SE) ∧
      f v ∈ BOnly} := by
  classical
  let RetainedOutside : Type v :=
    {e : E // e ∉ SE ∧ f (iOldR e) ∈ BOnly}
  let OldOutside : Type v :=
    {v : V //
      v ∉ (iOldL '' (Set.univ : Set OL) ∪ iOldR '' SE) ∧
      f v ∈ BOnly}
  let NewOutside : Type v :=
    {w : W //
      w ∉ (iNewL '' (Set.univ : Set NL) ∪ iNewR '' SE) ∧
      g w ∈ BOnly}
  let toOld : RetainedOutside → OldOutside := fun e =>
    ⟨iOldR e.1,
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hOldFree SE hRootE (iOldR e.1)).mpr
        ⟨e.1, e.2.1, rfl⟩,
      e.2.2⟩
  let toNew : RetainedOutside → NewOutside := fun e =>
    ⟨iNewR e.1,
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hNewFree SE hRootE (iNewR e.1)).mpr
        ⟨e.1, e.2.1, rfl⟩,
      by rw [hSameE]; exact e.2.2⟩
  have hOldInjective : Function.Injective toOld := by
    intro e e' heq
    apply Subtype.ext
    apply iOldR.injective
    exact congrArg Subtype.val heq
  have hNewInjective : Function.Injective toNew := by
    intro e e' heq
    apply Subtype.ext
    apply iNewR.injective
    exact congrArg Subtype.val heq
  have hOldSurjective : Function.Surjective toOld := by
    intro v
    obtain ⟨e, heOut, heEq⟩ :=
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hOldFree SE hRootE v.1).mp v.2.1
    have heB : f (iOldR e) ∈ BOnly := by
      rw [heEq]
      exact v.2.2
    refine ⟨⟨e, heOut, heB⟩, ?_⟩
    exact Subtype.ext heEq
  have hNewSurjective : Function.Surjective toNew := by
    intro w
    obtain ⟨e, heOut, heEq⟩ :=
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hNewFree SE hRootE w.1).mp w.2.1
    have heB : f (iOldR e) ∈ BOnly := by
      rw [← hSameE e, heEq]
      exact w.2.2
    refine ⟨⟨e, heOut, heB⟩, ?_⟩
    exact Subtype.ext heEq
  let oldEquiv : RetainedOutside ≃ OldOutside :=
    Equiv.ofBijective toOld ⟨hOldInjective, hOldSurjective⟩
  let newEquiv : RetainedOutside ≃ NewOutside :=
    Equiv.ofBijective toNew ⟨hNewInjective, hNewSurjective⟩
  letI : Fintype NewOutside := Fintype.ofFinite _
  letI : Fintype OldOutside := Fintype.ofFinite _
  have hCard : Fintype.card NewOutside = Fintype.card OldOutside :=
    Fintype.card_congr (newEquiv.symm.trans oldEquiv)
  simpa only [Nat.card_eq_fintype_card] using hCard

/-- The whole finite SOURCE support is partitioned exactly into
inside-Context and outside-Context supports, without counting
distinct images of the target map. Works for arbitrary finite
carriers and any target subset. -/
theorem finiteSourceSupport_card_split
    {V T : Type v}
    [Finite V]
    (f : V → T) (Context : Set V) (BOnly : Set T) :
    Nat.card {v : V // f v ∈ BOnly} =
      Nat.card {v : V // v ∈ Context ∧ f v ∈ BOnly} +
      Nat.card {v : V // v ∉ Context ∧ f v ∈ BOnly} := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let split :
      {v : V // f v ∈ BOnly} ≃
        ({v : V // v ∈ Context ∧ f v ∈ BOnly} ⊕
         {v : V // v ∉ Context ∧ f v ∈ BOnly}) where
    toFun := fun z =>
      if hz : z.1 ∈ Context then
        Sum.inl ⟨z.1, hz, z.2⟩
      else
        Sum.inr ⟨z.1, hz, z.2⟩
    invFun := fun z =>
      match z with
      | .inl a => ⟨a.1, a.2.2⟩
      | .inr b => ⟨b.1, b.2.2⟩
    left_inv := by
      intro z
      by_cases hz : z.1 ∈ Context <;> simp [hz]
    right_inv := by
      intro z
      cases z with
      | inl a => simp [a.2.1]
      | inr b => simp [b.2.1]
  have hCard := Fintype.card_congr split
  simpa only [Nat.card_eq_fintype_card, Fintype.card_sum] using hCard

/-- If TOTAL source support strictly drops while the support OUTSIDE
a selected pair of contexts remains exactly the same, then support
INSIDE those contexts strictly drops as well.

This is the finite source-counting step needed for an iteration
of genuine B-only piece flips INSIDE an outer mixed piece. The
assumption of total strict drop refers to one ACTUAL replacement,
not two separately chosen forbidden witnesses. -/
theorem finiteSourceSupport_strict_inside_of_outside_eq
    {V W T : Type v}
    [Finite V] [Finite W]
    (f : V → T) (g : W → T)
    (OldContext : Set V) (NewContext : Set W)
    (BOnly : Set T)
    (hStrictGlobal :
      Nat.card {w : W // g w ∈ BOnly} <
        Nat.card {v : V // f v ∈ BOnly})
    (hOutsideSame :
      Nat.card {w : W // w ∉ NewContext ∧ g w ∈ BOnly} =
        Nat.card {v : V // v ∉ OldContext ∧ f v ∈ BOnly}) :
    Nat.card {w : W // w ∈ NewContext ∧ g w ∈ BOnly} <
      Nat.card {v : V // v ∈ OldContext ∧ f v ∈ BOnly} := by
  have hOldSplit :=
    finiteSourceSupport_card_split f OldContext BOnly
  have hNewSplit :=
    finiteSourceSupport_card_split g NewContext BOnly
  omega

/-- For two actual free native functional amalgams sharing their
entire right-side source complement, a genuine global B-support
decrease along ONE replacement implies a LOCAL B-support decrease
inside the corresponding transported contexts, provided both
include their full embedded left pieces and the same right subset.

This is the precise quantitative contextual flip invariant. It
does not claim the new context is a minimal-separator geometric
piece or that its Myhill–Nerode profile equals the old one. -/
theorem fullFreeAmalgam_contextLocal_support_lt_of_global
    {H OL NL E V W T : Type v}
    [Finite V] [Finite W] [Finite E]
    {Root : Structure L H}
    {OldLeft : Structure L OL}
    {NewLeft : Structure L NL}
    {Right : Structure L E}
    {Old : Structure L V}
    {New : Structure L W}
    {sOldL : Structure.Embedding Root OldLeft}
    {sNewL : Structure.Embedding Root NewLeft}
    {sR : Structure.Embedding Root Right}
    {iOldL : Structure.Embedding OldLeft Old}
    {iOldR : Structure.Embedding Right Old}
    {iNewL : Structure.Embedding NewLeft New}
    {iNewR : Structure.Embedding Right New}
    (hOldFree : Structure.IsFreeAmalgam sOldL sR iOldL iOldR)
    (hNewFree : Structure.IsFreeAmalgam sNewL sR iNewL iNewR)
    (SE : Set E) (hRootE : ∀ r : H, sR r ∈ SE)
    (f : V → T) (g : W → T) (BOnly : Set T)
    (hSameE : ∀ e : E, g (iNewR e) = f (iOldR e))
    (hStrictGlobal :
      Nat.card {w : W // g w ∈ BOnly} <
        Nat.card {v : V // f v ∈ BOnly}) :
    Nat.card {w : W //
      w ∈ (iNewL '' (Set.univ : Set NL) ∪ iNewR '' SE) ∧
      g w ∈ BOnly} <
    Nat.card {v : V //
      v ∈ (iOldL '' (Set.univ : Set OL) ∪ iOldR '' SE) ∧
      f v ∈ BOnly} := by
  exact finiteSourceSupport_strict_inside_of_outside_eq
    f g
    (iOldL '' (Set.univ : Set OL) ∪ iOldR '' SE)
    (iNewL '' (Set.univ : Set NL) ∪ iNewR '' SE)
    BOnly hStrictGlobal
    (fullFreeAmalgam_contextOutside_support_card_eq
      hOldFree hNewFree SE hRootE f g BOnly hSameE)


end AllThoseRamseyClasses.Lifts
