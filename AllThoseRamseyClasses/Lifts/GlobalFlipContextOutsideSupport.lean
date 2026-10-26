import AllThoseRamseyClasses.Lifts.GlobalFlipOuterContextOutside

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

end AllThoseRamseyClasses.Lifts
