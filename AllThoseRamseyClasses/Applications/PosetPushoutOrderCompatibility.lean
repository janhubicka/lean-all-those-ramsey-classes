import AllThoseRamseyClasses.Applications.PosetPushoutRightReflection
import AllThoseRamseyClasses.Applications.OrderedPosetClass

/-!
# Compatible vertex linear order makes the poset pushout antisymmetric

Take ANY total linear order on the strong vertex pushout extending
the two original vertex orders. For the root-factorized partial-order
relation the cross comparison x<y has a root witness between the
two vertices; either one or both side inequalities are strict. Thus
this relation respects the amalgamated linear order, is antisymmetric,
and retains the two original partial orders as full induced relations.

The common-root compatible linear order was already constructed by
`ambient_ordered_pushout_exists`. The final wrapper combining this
with the original three-symbol language and its empty auxiliary
relation remains separate.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

private theorem poset_right_private_map
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (x : {b : F // b ∉ Set.range sR}) :
    FreeAmalgam.rightEmbedding Root Left Right sL sR x.1 =
      Sum.inr ((), x) := by
  change Attachment.copyMap Right
      (FreeAmalgam.support Root Left Right sL sR)
      Left (fun _ : Unit =>
        FreeAmalgam.overlapEmbedding Root Left Right sL sR)
      () x.1 = Sum.inr ((), x)
  exact Attachment.copyMap_not_mem () x.1 x.2

/-- A cross-side partial-order comparison must progress strictly
in the merged linear order. No extra convexity of the common root
or of the old posets is assumed. -/
theorem posetPushoutRelation_strict_order
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hLeft : orderedPosetClass Left)
    (hRight : orderedPosetClass Right)
    (o : LinearOrder (FreeAmalgam.Vertex Root Left Right sL sR))
    (hOrderL : ∀ a b : E, edge Left .lt a b →
      @LT.lt _ o.toLT
        (FreeAmalgam.leftEmbedding Root Left Right sL sR a)
        (FreeAmalgam.leftEmbedding Root Left Right sL sR b))
    (hOrderR : ∀ a b : F, edge Right .lt a b →
      @LT.lt _ o.toLT
        (FreeAmalgam.rightEmbedding Root Left Right sL sR a)
        (FreeAmalgam.rightEmbedding Root Left Right sL sR b))
    (x y : FreeAmalgam.Vertex Root Left Right sL sR)
    (hNE : x ≠ y)
    (hRel : posetPushoutRelation Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv) x y) :
    @LT.lt _ o.toLT x y := by
  classical
  letI : LinearOrder (FreeAmalgam.Vertex Root Left Right sL sR) := o
  rcases x with a | ⟨_, a⟩ <;> rcases y with b | ⟨_, b⟩
  · have hab : a ≠ b := by
      intro heq
      apply hNE
      exact congrArg Sum.inl heq
    have hp : edge Left .equiv a b := hRel
    exact hOrderL a b
      (hLeft.2.2.2.2.1 a b hab hp)
  · rcases hRel with ⟨d, had, hdb⟩
    have hPrivate : sR d ≠ b.1 := by
      intro hEq
      exact b.2 ⟨d, hEq⟩
    have hRlt : edge Right .lt (sR d) b.1 :=
      hRight.2.2.2.2.1 (sR d) b.1 hPrivate hdb
    have hRootToPrivate := hOrderR (sR d) b.1 hRlt
    have hOverlap := FreeAmalgam.left_right_overlap
      Root Left Right sL sR d
    have hFresh := poset_right_private_map
      Root Left Right sL sR b
    rw [← hOverlap, hFresh] at hRootToPrivate
    by_cases hEq : a = sL d
    · subst a
      exact hRootToPrivate
    · have hLlt : edge Left .lt a (sL d) :=
        hLeft.2.2.2.2.1 a (sL d) hEq had
      exact lt_trans (hOrderL a (sL d) hLlt) hRootToPrivate
  · rcases hRel with ⟨d, had, hdb⟩
    have hPrivate : a.1 ≠ sR d := by
      intro hEq
      exact a.2 ⟨d, hEq.symm⟩
    have hRlt : edge Right .lt a.1 (sR d) :=
      hRight.2.2.2.2.1 a.1 (sR d) hPrivate had
    have hPrivateToRoot := hOrderR a.1 (sR d) hRlt
    have hOverlap := FreeAmalgam.left_right_overlap
      Root Left Right sL sR d
    have hFresh := poset_right_private_map
      Root Left Right sL sR a
    rw [hFresh, ← hOverlap] at hPrivateToRoot
    by_cases hEq : sL d = b
    · subst b
      exact hPrivateToRoot
    · have hLlt : edge Left .lt (sL d) b :=
        hLeft.2.2.2.2.1 (sL d) b hEq hdb
      exact lt_trans hPrivateToRoot
        (hOrderL (sL d) b hLlt)
  · have hab : a.1 ≠ b.1 := by
      intro hEq
      apply hNE
      have hab : a = b := Subtype.ext hEq
      rw [hab]
    have hp : edge Right .equiv a.1 b.1 := hRel
    have hPrivateOrd : edge Right .lt a.1 b.1 :=
      hRight.2.2.2.2.1 a.1 b.1 hab hp
    have hOldOrder := hOrderR a.1 b.1 hPrivateOrd
    rw [poset_right_private_map Root Left Right sL sR a,
      poset_right_private_map Root Left Right sL sR b] at hOldOrder
    exact hOldOrder

/-- The poset pushout is antisymmetric because it is contained in
ONE total linear order whose strict part contains every nontrivial
positive comparison. -/
theorem posetPushoutRelation_antisymm
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (hLeft : orderedPosetClass Left)
    (hRight : orderedPosetClass Right)
    (o : LinearOrder (FreeAmalgam.Vertex Root Left Right sL sR))
    (hOrderL : ∀ a b : E, edge Left .lt a b →
      @LT.lt _ o.toLT
        (FreeAmalgam.leftEmbedding Root Left Right sL sR a)
        (FreeAmalgam.leftEmbedding Root Left Right sL sR b))
    (hOrderR : ∀ a b : F, edge Right .lt a b →
      @LT.lt _ o.toLT
        (FreeAmalgam.rightEmbedding Root Left Right sL sR a)
        (FreeAmalgam.rightEmbedding Root Left Right sL sR b))
    (x y : FreeAmalgam.Vertex Root Left Right sL sR)
    (hxy : posetPushoutRelation Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv) x y)
    (hyx : posetPushoutRelation Root Left Right sL sR
      (edge Left .equiv) (edge Right .equiv) y x) :
    x = y := by
  by_contra hNE
  have hlt := posetPushoutRelation_strict_order
    Root Left Right sL sR hLeft hRight o hOrderL hOrderR
    x y hNE hxy
  have hgt := posetPushoutRelation_strict_order
    Root Left Right sL sR hLeft hRight o hOrderL hOrderR
    y x (Ne.symm hNE) hyx
  letI : LinearOrder (FreeAmalgam.Vertex Root Left Right sL sR) := o
  exact (lt_asymm hlt hgt).elim

end AllThoseRamseyClasses.Applications.OrderedPosets
