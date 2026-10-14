import AllThoseRamseyClasses.Applications.PosetFinalInterface
import AllThoseRamseyClasses.Applications.PosetWeakLocalLaws
import AllThoseRamseyClasses.Applications.PosetLocalTestTransport
import AllThoseRamseyClasses.Applications.PosetExactWeakCompletion

/-!
# Finite ordered posets: the complete corrected 2019 application

The actual 2019 corrected Definition 2.17(4) allows an arbitrary WEAK
candidate C and a protected (possibly noninjective) map into an
original ambient Ramsey control C0. Its exact weak induced subsets
must be tested at the cutoff |C0|. We make no assumption that C is
itself already ordered, a partial order, or a member of K.

For empty closure descriptions, the corrected 4b singleton and
positive-pair tests force the actual source laws. The corrected 4c
completions yield genuine reflexive/transitive local relations on
the ORIGINAL bounded weak subsets, with reflection on positive
old vertex-order pairs. The checked all-path quasi-cycle theorem
then constructs a global poset on the SAME vertex set.

The construction changes the old incomplete vertex order only
where no old positive tuple determined an ordered pair, and it
reflects the original partial-order relation on old ordered pairs.
Consequently every existing full copy of any K-member B stays a
full induced copy. This supplies the exact B-copywise completion.

The theorem below discharges the last real class field and invokes
the fully proved corrected relational main Ramsey theorem, without
a native rank-increment or completion constructor hypothesis.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published
open AllThoseRamseyClasses.Applications
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

/-- The exact original weak local test cutoff |C0| works for all
finite ordered-poset B and every ORIGINAL ambient ordered C0. -/
theorem orderedPoset_exactLocalAtControlCard :
    OrderedPosetExactLocalAtControlCard := by
  intro X Y hFiniteX hFiniteY B C0 hBK hC0
  intro V hFiniteV C _hClosed hControl hTests hSmall
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype Y := Fintype.ofFinite Y
  letI : LinearOrder Y := ambientLinearOrder C0 hC0
  obtain ⟨_hControlIrred, f, hf⟩ := hControl
  have hRefl : ∀ x : V, edge C .equiv x x :=
    poset_weak_equiv_refl C hTests
  have hSubset : ∀ x y : V,
      edge C .equiv x y →
        (x = y ∨ edge C .lt x y) := by
    intro x y hxy
    by_cases heq : x = y
    · exact Or.inl heq
    · exact Or.inr (poset_weak_equiv_implies_lt C hTests x y heq hxy)
  have hStrictControl : ∀ x y : V,
      x ≠ y → (x = y ∨ edge C .lt x y) → f x < f y := by
    intro x y hne hord
    rcases hord with heq | hOld
    · exact (hne heq).elim
    · have hMapped : C0.rel .lt (f ∘ ![x,y]) :=
        hf.1 .lt ![x,y] hOld
      have ht : f ∘ ![x,y] = ![f x, f y] := by
        funext i
        fin_cases i <;> rfl
      have hC0Order : edge C0 .lt (f x) (f y) := by
        change C0.rel .lt ![f x, f y]
        rw [← ht]
        exact hMapped
      exact (ambientLinearOrder_lt_iff C0 hC0 (f x) (f y)).mpr hC0Order
  have hSmall' : ∀ S : Finset V, S.card ≤ Fintype.card Y →
      HasInducedClosedUKCompletion orderedPosetClass
        (∅ : ClosureDescription Lang)
        (C.induce (↑S : Set V)) := by
    intro S hs
    exact hSmall S (by simpa only [Nat.card_eq_fintype_card] using hs)
  have hLocal : ∀ S : Finset V, S.card ≤ Fintype.card Y →
      ∃ q : V → V → Prop,
        (∀ a : V, q a a) ∧
        (∀ a b c : V, q a b → q b c → q a c) ∧
        (∀ x y, x ∈ S → y ∈ S →
          edge C .equiv x y → q x y) ∧
        (∀ x y, x ∈ S → y ∈ S →
          (x = y ∨ edge C .lt x y) → q x y →
          edge C .equiv x y) :=
    poset_exact_weak_completions_supply_local_relations C hRefl hSmall'
  obtain ⟨o, q, hqRefl, hqTrans, hqAnti, hqPreserve, hqOrder,
      hOrderPreserve, hqReflect⟩ :=
    poset_reflexive_completion_of_exact_weak_local_tests
      (fun x y : V => x = y ∨ edge C .lt x y)
      (edge C .equiv) f hStrictControl hSubset hRefl hLocal
  letI : LinearOrder V := o
  let Target : RelStructure Lang V := {
    rel := fun
      | .lt, t => @LT.lt V o.toLT (t 0) (t 1)
      | .equiv, t => q (t 0) (t 1)
      | .mate, _ => False
  }
  have hTarget : orderedPosetClass Target := by
    refine ⟨⟨inferInstance, ?_, ?_, ?_⟩,
      hqRefl, hqTrans, hqAnti, ?_, ?_⟩
    · intro x hxx
      exact (lt_irrefl x hxx).elim
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
    · intro x y hne hxy
      exact hqOrder x y hne hxy
    · intro x y h
      exact h
  refine ⟨V, inferInstance, Target, hTarget, (fun x : V => x), ?_⟩
  intro b
  have hOrderB : ∀ x y : X,
      (@LT.lt V o.toLT (b x) (b y)) ↔
        edge B .lt x y := by
    intro x y
    constructor
    · intro hTargetLt
      by_cases heq : x = y
      · subst y
        exact (lt_irrefl _ hTargetLt).elim
      · rcases hBK.1.2.2.2 x y heq with hxy | hyx
        · exact hxy
        · have hOldC : edge C .lt (b y) (b x) :=
            (edge_embedding_iff b .lt y x).mpr hyx
          have hNewReverse : @LT.lt V o.toLT (b y) (b x) :=
            hOrderPreserve (b y) (b x)
              (fun h => heq (b.injective h.symm))
              (Or.inr hOldC)
          exact (lt_asymm hTargetLt hNewReverse).elim
    · intro hOldB
      have hOldC : edge C .lt (b x) (b y) :=
        (edge_embedding_iff b .lt x y).mpr hOldB
      have hNe : b x ≠ b y := by
        intro heq
        have hxy : x = y := b.injective heq
        subst y
        exact hBK.1.2.1 x hOldB
      exact hOrderPreserve (b x) (b y) hNe (Or.inr hOldC)
  have hEquivB : ∀ x y : X,
      q (b x) (b y) ↔ edge B .equiv x y := by
    intro x y
    constructor
    · intro hq
      by_cases heq : x = y
      · subst y
        exact hBK.2.1 x
      · have hNe : b x ≠ b y :=
          fun h => heq (b.injective h)
        have hTargetLt : @LT.lt V o.toLT (b x) (b y) :=
          hqOrder (b x) (b y) hNe hq
        have hOldB : edge B .lt x y :=
          (hOrderB x y).mp hTargetLt
        have hOldC : edge C .lt (b x) (b y) :=
          (edge_embedding_iff b .lt x y).mpr hOldB
        have hCEquiv : edge C .equiv (b x) (b y) :=
          (hqReflect (b x) (b y) (Or.inr hOldC)).mp hq
        exact (edge_embedding_iff b .equiv x y).mp hCEquiv
    · intro hOldB
      have hOldC : edge C .equiv (b x) (b y) :=
        (edge_embedding_iff b .equiv x y).mpr hOldB
      exact hqPreserve (b x) (b y) hOldC
  let bTarget : Embedding B Target := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R t
      have ht : t = ![t 0, t 1] := by
        funext i
        fin_cases i <;> rfl
      rw [ht]
      cases R with
      | lt =>
          change (@LT.lt V o.toLT (b (t 0)) (b (t 1))) ↔
            edge B .lt (t 0) (t 1)
          exact hOrderB _ _
      | equiv =>
          change q (b (t 0)) (b (t 1)) ↔
            edge B .equiv (t 0) (t 1)
          exact hEquivB _ _
      | mate =>
          change False ↔ edge B .mate (t 0) (t 1)
          exact (iff_false_intro (hBK.2.2.2.2.2 (t 0) (t 1))).symm
  }
  exact ⟨bTarget, fun x => rfl⟩

/-- All original class hypotheses, including the fixed exact local
cutoff n(B,C0)=|C0|, now follow for finite ordered posets. -/
theorem orderedPoset_isCoordinated2019Multiamalgamation :
    IsCoordinated2019MultiamalgamationClass
      orderedAmbientClass orderedPosetClass
      (∅ : ClosureDescription Lang) :=
  orderedPoset_coordinatedClass_of_exactLocal
    orderedPoset_exactLocalAtControlCard

/-- The finite class of posets with a chosen linear extension is
Ramsey, as a genuine *application* of the proved corrected relational
2019 theorem. This declaration has NO local-completion premise. -/
theorem orderedPoset_isRamsey :
    FiniteRamseyClass orderedPosetClass :=
  orderedPoset_ramsey_of_exactLocal
    orderedPoset_exactLocalAtControlCard

end AllThoseRamseyClasses.Applications.OrderedPosets
