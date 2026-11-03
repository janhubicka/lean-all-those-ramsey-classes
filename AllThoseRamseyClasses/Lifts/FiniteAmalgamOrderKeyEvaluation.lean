import AllThoseRamseyClasses.Lifts.FiniteAmalgamOrderKey

/-!
# Track E: evaluate the exact finite strong-amalgam lexicographic key

The already constructed injective key classifies target vertices as
an embedded common-root point, Y-private, Z-private, or target-extra.
These predicates cannot be treated as interchangeable: the
Y-private and Z-private definitions are meaningful only under
the EXACT strong intersection law for the two embeddings.

We establish the literal closed forms of the key on these
categories. Common root vertices have the intrinsic root rank.
A private side vertex has its exact common-root cut rank and its
side's intrinsic order rank. Target extras lie after every possible
common-root cut.

These are mathematical evaluation lemmas, not a theorem that the
induced target order already extends either side order. The latter
requires comparing the first differing key coordinate for EVERY
ordered pair, under strict monotonicity of the root embeddings.
No full-functional data or Ramsey property is postulated.

This module depends on the finite injective order key proof PR #853,
which must independently pass complete CI before it can be used
as a certified ingredient.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

/-- The finite target order key has the exact common-root rank
on the image of the shared ordered root, provided that both
the root-to-Y and Y-to-target maps are injective.

No assumption about the other side Z is needed here. -/
theorem finiteAmalgamOrderKey_on_root
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hsY : Function.Injective sY)
    (hjY : Function.Injective jY)
    (x : X) :
    finiteAmalgamOrderKey sY sZ jY jZ (jY (sY x)) =
      toLex (StructuralRamsey.Rooted.orderRank X x,
        toLex ((2 : ℕ),
          toLex ((0 : ℕ), Fintype.equivFin T (jY (sY x))))) := by
  classical
  have hRoot : ∃ r : X, jY (sY r) = jY (sY x) := ⟨x, rfl⟩
  have hChosen : Classical.choose hRoot = x :=
    hsY (hjY (Classical.choose_spec hRoot))
  simp only [finiteAmalgamOrderKey, dif_pos hRoot, hChosen]

/-- Exact key formula on a Y-private vertex.
The Y-vertex is not the image of a root coordinate, and
its target-image has a unique Y source preimage. -/
theorem finiteAmalgamOrderKey_on_Y_private
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hjY : Function.Injective jY)
    (y : Y)
    (hPrivate : ¬ ∃ x : X, sY x = y) :
    finiteAmalgamOrderKey sY sZ jY jZ (jY y) =
      toLex (finiteRootCutRank sY y,
        toLex ((0 : ℕ),
          toLex (StructuralRamsey.Rooted.orderRank Y y,
            Fintype.equivFin T (jY y)))) := by
  classical
  have hNoRoot : ¬ ∃ x : X, jY (sY x) = jY y := by
    rintro ⟨x, hx⟩
    exact hPrivate ⟨x, hjY hx⟩
  have hY : ∃ z : Y, jY z = jY y := ⟨y, rfl⟩
  have hChosen : Classical.choose hY = y :=
    hjY (Classical.choose_spec hY)
  simp only [finiteAmalgamOrderKey, dif_neg hNoRoot,
    dif_pos hY, hChosen]

/-- Exact key formula on a Z-private vertex under the
FULL strong-amalgam overlap law. The law is essential:
without it, a Z-private image could also be a Y-image and
would have been assigned Y's category by the key definition. -/
theorem finiteAmalgamOrderKey_on_Z_private
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (hjZ : Function.Injective jZ)
    (hOverlap : ∀ y : Y, ∀ z : Z,
      jY y = jZ z ↔
        ∃ x : X, y = sY x ∧ z = sZ x)
    (z : Z)
    (hPrivate : ¬ ∃ x : X, sZ x = z) :
    finiteAmalgamOrderKey sY sZ jY jZ (jZ z) =
      toLex (finiteRootCutRank sZ z,
        toLex ((1 : ℕ),
          toLex (StructuralRamsey.Rooted.orderRank Z z,
            Fintype.equivFin T (jZ z)))) := by
  classical
  have hNotY : ¬ ∃ y : Y, jY y = jZ z := by
    rintro ⟨y, hy⟩
    obtain ⟨x, _hX, hz⟩ := (hOverlap y z).mp hy
    exact hPrivate ⟨x, hz.symm⟩
  have hNotRoot : ¬ ∃ x : X, jY (sY x) = jZ z := by
    rintro ⟨x, hx⟩
    exact hNotY ⟨sY x, hx⟩
  have hZ : ∃ w : Z, jZ w = jZ z := ⟨z, rfl⟩
  have hChosen : Classical.choose hZ = z :=
    hjZ (Classical.choose_spec hZ)
  simp only [finiteAmalgamOrderKey, dif_neg hNotRoot,
    dif_neg hNotY, dif_pos hZ, hChosen]

/-- Every target-extra vertex has cut index larger than all
possible root cut ranks, and category 3. No overlap
hypothesis is needed to state this formula; both side
image exclusions are explicit. -/
theorem finiteAmalgamOrderKey_on_extra
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (t : T)
    (hNotY : ¬ ∃ y : Y, jY y = t)
    (hNotZ : ¬ ∃ z : Z, jZ z = t) :
    finiteAmalgamOrderKey sY sZ jY jZ t =
      toLex ((Fintype.card X + 1 : ℕ),
        toLex ((3 : ℕ),
          toLex ((0 : ℕ), Fintype.equivFin T t))) := by
  classical
  have hNotRoot : ¬ ∃ x : X, jY (sY x) = t := by
    rintro ⟨x, hx⟩
    exact hNotY ⟨sY x, hx⟩
  simp only [finiteAmalgamOrderKey, dif_neg hNotRoot,
    dif_neg hNotY, dif_neg hNotZ]

end AllThoseRamseyClasses.Lifts
