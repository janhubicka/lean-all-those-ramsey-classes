import AllThoseRamseyClasses.Applications.SteinerOrderPushout
import AllThoseRamseyClasses.Applications.SteinerFreeAmalgamClosure
import PartiteConstruction.Ramsey.CompatibleClassCompletion

/-!
# Strong amalgamation for freely ordered partial Steiner triples

The construction takes the real strong vertex free amalgam, preserves all
covered-pair and block tuples exactly, and replaces only the incomplete
union of the two vertex orders by a compatible total order. Full embeddings
on both sides are proved, and the Steiner axioms are then checked on the
same finite vertex set.

Unlike a partial ordinary hypergraph embedding, the full covered-pair
relation here reflects the domain of the ternary closure operation.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- In the genuine free amalgam, each positive covered pair belongs
entirely to one of the two old sides. -/
private theorem covered_pair_from_one_side
    {H E F P : Type}
    {Root : RelStructure Lang H}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    {x y : P}
    (h : edge Whole .covered x y) :
    (∃ a b : E, edge Left .covered a b ∧ x = iL a ∧ y = iL b) ∨
    (∃ a b : F, edge Right .covered a b ∧ x = iR a ∧ y = iR b) := by
  have ht : Whole.rel .covered ![x,y] := h
  rcases (hFree.rel_iff .covered ![x,y]).mp ht with
      ⟨t, hRel, hEq⟩ | ⟨t, hRel, hEq⟩
  · left
    refine ⟨t 0, t 1, ?_, ?_, ?_⟩
    · change Left.rel .covered ![t 0, t 1]
      have ht : (![t 0, t 1] : Fin 2 → E) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1
  · right
    refine ⟨t 0, t 1, ?_, ?_, ?_⟩
    · change Right.rel .covered ![t 0, t 1]
      have ht : (![t 0, t 1] : Fin 2 → F) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1

/-- The same side localization works for each complete block tuple. -/
private theorem block_from_one_side
    {H E F P : Type}
    {Root : RelStructure Lang H}
    {Left : RelStructure Lang E} {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    {x y z : P}
    (h : triple Whole x y z) :
    (∃ a b c : E, triple Left a b c ∧
      x = iL a ∧ y = iL b ∧ z = iL c) ∨
    (∃ a b c : F, triple Right a b c ∧
      x = iR a ∧ y = iR b ∧ z = iR c) := by
  have ht : Whole.rel .block ![x,y,z] := h
  rcases (hFree.rel_iff .block ![x,y,z]).mp ht with
      ⟨t, hRel, hEq⟩ | ⟨t, hRel, hEq⟩
  · left
    refine ⟨t 0, t 1, t 2, ?_, ?_, ?_, ?_⟩
    · change Left.rel .block ![t 0, t 1, t 2]
      have ht : (![t 0, t 1, t 2] : Fin 3 → E) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1
    · simpa only [Function.comp_apply] using congrFun hEq 2
  · right
    refine ⟨t 0, t 1, t 2, ?_, ?_, ?_, ?_⟩
    · change Right.rel .block ![t 0, t 1, t 2]
      have ht : (![t 0, t 1, t 2] : Fin 3 → F) = t := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      exact hRel
    · simpa only [Function.comp_apply] using congrFun hEq 0
    · simpa only [Function.comp_apply] using congrFun hEq 1
    · simpa only [Function.comp_apply] using congrFun hEq 2

/-- Unique completion of a covered pair follows from intrinsic
closedness; we use the exact original root, not a newly generated hull. -/
private theorem block_unique_of_closed
    {P : Type} (C : RelStructure Lang P)
    (hC : IsUClosed blockRules C)
    {x y z w : P}
    (hz : triple C x y z) (hw : triple C x y w) :
    z = w := by
  have hRule : blockRule ∈ blockRules := by simp [blockRules]
  obtain ⟨e, he⟩ := (hC blockRule hRule).1 ![x,y,z] hz
  have he0 : e 0 = x := (he 0).symm
  have he1 : e 1 = y := (he 1).symm
  obtain ⟨t, _ht, hUnique⟩ := (hC blockRule hRule).2 e
  have hzMatch : ∀ i : Fin 2,
      (![x,y,z] : Fin 3 → P) (i.castLE blockRule.rootLE) = e i := by
    intro i
    fin_cases i
    · exact he0.symm
    · exact he1.symm
  have hwMatch : ∀ i : Fin 2,
      (![x,y,w] : Fin 3 → P) (i.castLE blockRule.rootLE) = e i := by
    intro i
    fin_cases i
    · exact he0.symm
    · exact he1.symm
  have hZ : (![x,y,z] : Fin 3 → P) = t := hUnique _ ⟨hz, hzMatch⟩
  have hW : (![x,y,w] : Fin 3 → P) = t := hUnique _ ⟨hw, hwMatch⟩
  have hEq : (![x,y,z] : Fin 3 → P) = ![x,y,w] :=
    hZ.trans hW.symm
  exact congrFun hEq 2

/-- The freely ordered marked-pair representation is a genuine
strong amalgamation class, not merely closed under free union of
its non-order relations. -/
theorem orderedSteinerClass_strongAmalgamation :
    HasFiniteStrongAmalgamation orderedSteinerClass := by
  intro H E F hFiniteH hFiniteE hFiniteF Root Left Right
    hRoot hLeft hRight sL sR
  classical
  let P := FreeAmalgam.Vertex Root Left Right sL sR
  let G := FreeAmalgam.amalgam Root Left Right sL sR
  let iL := FreeAmalgam.leftEmbedding Root Left Right sL sR
  let iR := FreeAmalgam.rightEmbedding Root Left Right sL sR
  have hP : Finite P := inferInstance
  letI : Finite P := hP
  let hFree : IsFreeAmalgam sL sR iL iR :=
    FreeAmalgam.isFreeAmalgam Root Left Right sL sR
  obtain ⟨o, hOrdL, hOrdR⟩ :=
    steiner_freeAmalgam_order_extension hFree hLeft hRight
  letI : LinearOrder P := o
  let Target : RelStructure Lang P := {
    rel := fun
      | .order, t => @LT.lt P o.toLT (t 0) (t 1)
      | .covered, t => G.rel .covered t
      | .block, t => G.rel .block t
  }
  have hOrderL (a b : E) :
      (@LT.lt P o.toLT (iL a) (iL b)) ↔
        edge Left .order a b := by
    constructor
    · intro hNew
      by_cases heq : a = b
      · subst b
        exact (lt_irrefl _ hNew).elim
      · rcases hLeft.order_total a b heq with h | h
        · exact h
        · exact (lt_asymm hNew (hOrdL b a h)).elim
    · exact hOrdL a b
  have hOrderR (a b : F) :
      (@LT.lt P o.toLT (iR a) (iR b)) ↔
        edge Right .order a b := by
    constructor
    · intro hNew
      by_cases heq : a = b
      · subst b
        exact (lt_irrefl _ hNew).elim
      · rcases hRight.order_total a b heq with h | h
        · exact h
        · exact (lt_asymm hNew (hOrdR b a h)).elim
    · exact hOrdR a b
  let jL : Embedding Left Target := {
    toFun := iL
    injective := iL.injective
    map_rel_iff := by
      intro R t
      cases R with
      | order =>
        have ht : t = ![t 0, t 1] := by
          funext i
          fin_cases i <;> rfl
        rw [ht]
        change (@LT.lt P o.toLT (iL (t 0)) (iL (t 1))) ↔
          edge Left .order (t 0) (t 1)
        exact hOrderL _ _
      | covered =>
        exact iL.map_rel_iff .covered t
      | block =>
        exact iL.map_rel_iff .block t
  }
  let jR : Embedding Right Target := {
    toFun := iR
    injective := iR.injective
    map_rel_iff := by
      intro R t
      cases R with
      | order =>
        have ht : t = ![t 0, t 1] := by
          funext i
          fin_cases i <;> rfl
        rw [ht]
        change (@LT.lt P o.toLT (iR (t 0)) (iR (t 1))) ↔
          edge Right .order (t 0) (t 1)
        exact hOrderR _ _
      | covered =>
        exact iR.map_rel_iff .covered t
      | block =>
        exact iR.map_rel_iff .block t
  }
  have hGClosed : IsUClosed blockRules G :=
    steiner_freeAmalgam_blockRules_closed
      Root Left Right hRoot hLeft hRight sL sR
  have hTarget : orderedSteinerClass Target := by
    refine {
      finite := hP
      order_irrefl := ?_
      order_trans := ?_
      order_total := ?_
      covered_implies_order := ?_
      covered_root := ?_
      block_valid := ?_
      block_distinct := ?_
      covered_has_block := ?_
      block_unique := ?_
      other_pairs := ?_
    }
    · intro x hxx
      exact (lt_irrefl x hxx).elim
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
    · intro x y hxy
      rcases covered_pair_from_one_side hFree hxy with
        ⟨a,b,hab,rfl,rfl⟩ | ⟨a,b,hab,rfl,rfl⟩
      · exact hOrdL a b (hLeft.covered_implies_order a b hab)
      · exact hOrdR a b (hRight.covered_implies_order a b hab)
    · intro x y hxy
      rcases covered_pair_from_one_side hFree hxy with
        ⟨a,b,hab,rfl,rfl⟩ | ⟨a,b,hab,rfl,rfl⟩
      · obtain ⟨e, he0, he1⟩ := hLeft.covered_root a b hab
        exact ⟨jL.comp e, congrArg jL he0, congrArg jL he1⟩
      · obtain ⟨e, he0, he1⟩ := hRight.covered_root a b hab
        exact ⟨jR.comp e, congrArg jR he0, congrArg jR he1⟩
    · intro x y z hxyz
      rcases block_from_one_side hFree hxyz with
        ⟨a,b,c,habc,rfl,rfl,rfl⟩ |
        ⟨a,b,c,habc,rfl,rfl,rfl⟩
      · exact (edge_embedding_iff jL .covered a b).mpr
          (hLeft.block_valid a b c habc)
      · exact (edge_embedding_iff jR .covered a b).mpr
          (hRight.block_valid a b c habc)
    · intro x y z hxyz
      rcases block_from_one_side hFree hxyz with
        ⟨a,b,c,habc,rfl,rfl,rfl⟩ |
        ⟨a,b,c,habc,rfl,rfl,rfl⟩
      · obtain ⟨hab, hac, hbc⟩ := hLeft.block_distinct a b c habc
        exact ⟨fun h => hab (jL.injective h),
          fun h => hac (jL.injective h),
          fun h => hbc (jL.injective h)⟩
      · obtain ⟨hab, hac, hbc⟩ := hRight.block_distinct a b c habc
        exact ⟨fun h => hab (jR.injective h),
          fun h => hac (jR.injective h),
          fun h => hbc (jR.injective h)⟩
    · intro x y hxy
      rcases covered_pair_from_one_side hFree hxy with
        ⟨a,b,hab,rfl,rfl⟩ | ⟨a,b,hab,rfl,rfl⟩
      · obtain ⟨c,habc⟩ := hLeft.covered_has_block a b hab
        exact ⟨jL c, (triple_embedding_iff jL a b c).mpr habc⟩
      · obtain ⟨c,habc⟩ := hRight.covered_has_block a b hab
        exact ⟨jR c, (triple_embedding_iff jR a b c).mpr habc⟩
    · intro x y z w hz hw
      exact block_unique_of_closed G hGClosed hz hw
    · intro x y z hxyz
      rcases block_from_one_side hFree hxyz with
        ⟨a,b,c,habc,rfl,rfl,rfl⟩ |
        ⟨a,b,c,habc,rfl,rfl,rfl⟩
      · obtain ⟨hXZ, hYZ⟩ := hLeft.other_pairs a b c habc
        constructor
        · rcases hXZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
          · exact Or.inl ⟨(triple_embedding_iff jL a c b).mpr htr,
              hOrdL a c hord⟩
          · exact Or.inr ⟨(triple_embedding_iff jL c a b).mpr htr,
              hOrdL c a hord⟩
        · rcases hYZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
          · exact Or.inl ⟨(triple_embedding_iff jL b c a).mpr htr,
              hOrdL b c hord⟩
          · exact Or.inr ⟨(triple_embedding_iff jL c b a).mpr htr,
              hOrdL c b hord⟩
      · obtain ⟨hXZ, hYZ⟩ := hRight.other_pairs a b c habc
        constructor
        · rcases hXZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
          · exact Or.inl ⟨(triple_embedding_iff jR a c b).mpr htr,
              hOrdR a c hord⟩
          · exact Or.inr ⟨(triple_embedding_iff jR c a b).mpr htr,
              hOrdR c a hord⟩
        · rcases hYZ with ⟨htr, hord⟩ | ⟨htr, hord⟩
          · exact Or.inl ⟨(triple_embedding_iff jR b c a).mpr htr,
              hOrdR b c hord⟩
          · exact Or.inr ⟨(triple_embedding_iff jR c b a).mpr htr,
              hOrdR c b hord⟩
  refine ⟨P, hP, Target, hTarget, jL, jR, ?_, ?_⟩
  · exact FreeAmalgam.left_right_overlap Root Left Right sL sR
  · intro a b hEq
    exact (hFree.overlap a b).mp hEq

end AllThoseRamseyClasses.Applications.SteinerTriples
