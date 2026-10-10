import AllThoseRamseyClasses.Published.EquivalenceSideTags

/-!
# Shared labels for the two sides of an E-amalgam

Both side structures use the SAME quotient classes of the common
root. E-classes disjoint from the root get LEFT or RIGHT
tags, so they cannot be accidentally identified. The equality
of root tags is built in, and the two side-label maps separately
reflect the original E relation.

The global carrier P and its final E and order symbols are the
next separate steps. No strong amalgamation claim occurs here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Map common quotient tags unchanged and side-only tags into the
left summand of a disjoint union of private E-class labels. -/
def includeLeftClassTag {Q E F : Type} :
    Q ⊕ E → Q ⊕ (E ⊕ F)
  | .inl q => .inl q
  | .inr e => .inr (.inl e)

/-- The corresponding right-only labels, again preserving the
common-root component unchanged. -/
def includeRightClassTag {Q E F : Type} :
    Q ⊕ F → Q ⊕ (E ⊕ F)
  | .inl q => .inl q
  | .inr f => .inr (.inr f)

theorem includeLeftClassTag_injective {Q E F : Type} :
    Function.Injective (includeLeftClassTag (Q := Q) (E := E) (F := F)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [includeLeftClassTag]

theorem includeRightClassTag_injective {Q E F : Type} :
    Function.Injective (includeRightClassTag (Q := Q) (E := E) (F := F)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [includeRightClassTag]

/-- Shared-root class labels plus two independent families of private
quotient E-classes. -/
abbrev AmalgamClassLabels
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right) : Type :=
  Quotient (equivSetoid Root hRoot) ⊕
   (Quotient (equivSetoid Left hLeft) ⊕
    Quotient (equivSetoid Right hRight))

noncomputable def leftAmalgamTag
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (x : E) :
    AmalgamClassLabels Root Left Right hRoot hLeft hRight :=
  includeLeftClassTag (sideClassTag Root Left hRoot hLeft sL x)

noncomputable def rightAmalgamTag
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sR : Embedding Root Right) (y : F) :
    AmalgamClassLabels Root Left Right hRoot hLeft hRight :=
  includeRightClassTag (sideClassTag Root Right hRoot hRight sR y)

/-- Distinct E-classes in the left structure remain distinct global
labels. The common root is represented by its own quotient class. -/
theorem leftAmalgamTag_eq_iff
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (x y : E) :
    leftAmalgamTag Root Left Right hRoot hLeft hRight sL x =
      leftAmalgamTag Root Left Right hRoot hLeft hRight sL y ↔
        edge Left .equiv x y := by
  change
    includeLeftClassTag (sideClassTag Root Left hRoot hLeft sL x) =
      includeLeftClassTag (sideClassTag Root Left hRoot hLeft sL y) ↔
      edge Left .equiv x y
  constructor
  · intro h
    exact (sideClassTag_eq_iff Root Left hRoot hLeft sL x y).mp
      (includeLeftClassTag_injective h)
  · intro h
    exact congrArg includeLeftClassTag
      ((sideClassTag_eq_iff Root Left hRoot hLeft sL x y).mpr h)

/-- The same full E-reflection property on the right. -/
theorem rightAmalgamTag_eq_iff
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sR : Embedding Root Right) (x y : F) :
    rightAmalgamTag Root Left Right hRoot hLeft hRight sR x =
      rightAmalgamTag Root Left Right hRoot hLeft hRight sR y ↔
        edge Right .equiv x y := by
  change
    includeRightClassTag (sideClassTag Root Right hRoot hRight sR x) =
      includeRightClassTag (sideClassTag Root Right hRoot hRight sR y) ↔
      edge Right .equiv x y
  constructor
  · intro h
    exact (sideClassTag_eq_iff Root Right hRoot hRight sR x y).mp
      (includeRightClassTag_injective h)
  · intro h
    exact congrArg includeRightClassTag
      ((sideClassTag_eq_iff Root Right hRoot hRight sR x y).mpr h)

/-- The two side labels agree EXACTLY for each embedded root
vertex: the shared label is the corresponding quotient root class. -/
theorem amalgamTag_agree_on_root
    {D E F : Type}
    (Root : RelStructure Lang D) (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hRoot : pairedClass Root) (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (d : D) :
    leftAmalgamTag Root Left Right hRoot hLeft hRight sL (sL d) =
      rightAmalgamTag Root Left Right hRoot hLeft hRight sR (sR d) := by
  simp [leftAmalgamTag, rightAmalgamTag,
    sideClassTag_root Root Left hRoot hLeft sL d,
    sideClassTag_root Root Right hRoot hRight sR d,
    includeLeftClassTag, includeRightClassTag]

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
