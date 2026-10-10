import AllThoseRamseyClasses.Published.EquivalenceOverlapClasses

/-!
# Explicit quotient E-class labels on one side of an overlap

The strong amalgam will label each E-class that meets the common
root by its E-class in the root. Every class disjoint from the root
gets an independent side tag. This is a genuine quotient-class
construction, NOT a least-transitive-closure oracle.

This module proves all of the following without extra hypotheses:
  (i) a named root vertex gets its exact root quotient label;
 (ii) equal side labels are E-equivalent;
(iii) all E-equivalent side vertices have equal side labels.

Both sides of the amalgam will share the first quotient component;
their disjoint components are separately tagged in a later module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The actual equivalence relation as a quotient type. -/
def equivSetoid {V : Type}
    (C : RelStructure Lang V) (hC : pairedClass C) : Setoid V where
  r := edge C .equiv
  iseqv := hC.equiv

/-- Does a side E-class meet the image of the common root? -/
def MeetsRoot
    {D X : Type}
    {Root : RelStructure Lang D} {Side : RelStructure Lang X}
    (s : Embedding Root Side) (x : X) : Prop :=
  ∃ d : D, edge Side .equiv x (s d)

/-- Root classes receive a common label, while classes not
meeting the root keep a separate side-only quotient label. -/
noncomputable def sideClassTag
    {D X : Type}
    (Root : RelStructure Lang D) (Side : RelStructure Lang X)
    (hRoot : pairedClass Root) (hSide : pairedClass Side)
    (s : Embedding Root Side) (x : X) :
    Quotient (equivSetoid Root hRoot) ⊕
      Quotient (equivSetoid Side hSide) :=
  if h : MeetsRoot s x then
    Sum.inl (Quotient.mk (equivSetoid Root hRoot) (Classical.choose h))
  else
    Sum.inr (Quotient.mk (equivSetoid Side hSide) x)

/-- The E-class of an embedded root vertex is labelled by
its OWN root E-class, independently of how a witness is chosen. -/
theorem sideClassTag_root
    {D X : Type}
    (Root : RelStructure Lang D) (Side : RelStructure Lang X)
    (hRoot : pairedClass Root) (hSide : pairedClass Side)
    (s : Embedding Root Side) (d : D) :
    sideClassTag Root Side hRoot hSide s (s d) =
      Sum.inl (Quotient.mk (equivSetoid Root hRoot) d) := by
  classical
  have hx : MeetsRoot s (s d) :=
    ⟨d, hSide.equiv.refl (s d)⟩
  have hChoose : edge Root .equiv (Classical.choose hx) d := by
    apply (equivalence_embedding_iff s _ _).mp
    exact hSide.equiv.symm (Classical.choose_spec hx)
  simp only [sideClassTag, dif_pos hx]
  exact congrArg Sum.inl (Quotient.sound hChoose)

/-- Two vertices on the SAME side have the same tag exactly when
they are E-equivalent. In particular, the root-class labelling
never merges two originally distinct E-classes on either side. -/
theorem sideClassTag_eq_iff
    {D X : Type}
    (Root : RelStructure Lang D) (Side : RelStructure Lang X)
    (hRoot : pairedClass Root) (hSide : pairedClass Side)
    (s : Embedding Root Side) (x y : X) :
    sideClassTag Root Side hRoot hSide s x =
      sideClassTag Root Side hRoot hSide s y ↔
      edge Side .equiv x y := by
  classical
  by_cases hx : MeetsRoot s x
  · by_cases hy : MeetsRoot s y
    · constructor
      · intro he
        have hq :
            (Quotient.mk (equivSetoid Root hRoot) (Classical.choose hx)) =
              Quotient.mk (equivSetoid Root hRoot) (Classical.choose hy) := by
          simpa only [sideClassTag, dif_pos hx, dif_pos hy,
            Sum.inl.injEq] using he
        have hr : edge Root .equiv
            (Classical.choose hx) (Classical.choose hy) :=
          Quotient.exact hq
        have hs := (equivalence_embedding_iff s _ _).mpr hr
        exact hSide.equiv.trans (Classical.choose_spec hx)
          (hSide.equiv.trans hs
            (hSide.equiv.symm (Classical.choose_spec hy)))
      · intro hxy
        have hr : edge Root .equiv
            (Classical.choose hx) (Classical.choose hy) := by
          apply (equivalence_embedding_iff s _ _).mp
          exact hSide.equiv.trans
            (hSide.equiv.symm (Classical.choose_spec hx))
            (hSide.equiv.trans hxy (Classical.choose_spec hy))
        have heq := Quotient.sound hr
        simpa only [sideClassTag, dif_pos hx, dif_pos hy,
          Sum.inl.injEq] using heq
    · constructor
      · intro he
        have : False := by
          simpa only [sideClassTag, dif_pos hx, dif_neg hy,
            Sum.inl_ne_inr] using he
        exact this.elim
      · intro hxy
        apply False.elim
        apply hy
        obtain ⟨d, hd⟩ := hx
        exact ⟨d, hSide.equiv.trans (hSide.equiv.symm hxy) hd⟩
  · by_cases hy : MeetsRoot s y
    · constructor
      · intro he
        have : False := by
          simpa only [sideClassTag, dif_neg hx, dif_pos hy,
            Sum.inr_ne_inl] using he
        exact this.elim
      · intro hxy
        apply False.elim
        apply hx
        obtain ⟨d, hd⟩ := hy
        exact ⟨d, hSide.equiv.trans hxy hd⟩
    · constructor
      · intro he
        have hq :
            Quotient.mk (equivSetoid Side hSide) x =
              Quotient.mk (equivSetoid Side hSide) y := by
          simpa only [sideClassTag, dif_neg hx, dif_neg hy,
            Sum.inr.injEq] using he
        exact Quotient.exact hq
      · intro hxy
        have heq : Quotient.mk (equivSetoid Side hSide) x =
            Quotient.mk (equivSetoid Side hSide) y :=
          Quotient.sound hxy
        simpa only [sideClassTag, dif_neg hx, dif_neg hy,
          Sum.inr.injEq] using heq

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
