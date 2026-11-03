import AllThoseRamseyClasses.Lifts.FiniteOrderRootCuts
import Mathlib.Order.Prod.Lex.Basic

/-!
# Track E: the actual finite lexicographic key for ordered strong amalgams

Given finite ordered source sides Y,Z over a common finite ordered
root X, and maps jY:Y->T, jZ:Z->T to a finite target T, the
root-cut order construction gives EVERY target vertex one
lexicographic key with four coordinates:

1. number of common-root vertices strictly below it in its side;
2. its type: Y-private (0), Z-private (1), common root (2),
   or extra target vertex (3);
3. the intrinsic linear-order rank of a side-private vertex;
4. an arbitrary injective numerical tie-breaker on ALL target vertices.

A root vertex has its intrinsic rank in X as first coordinate,
and a target-extra vertex is placed after the final root gap.
The fourth coordinate makes the key genuinely injective
WITHOUT a root-overlap assumption. Thus it yields an ACTUAL
linear order on the target carrier even before verifying
the strong-amalgamation overlap compatibility.

The still open ordered strong-AP step is to show, under the
EXACT strong overlap law and strict monotonicity of the root maps,
that this chosen target order makes both side embeddings
strictly increasing. Those hypotheses are NOT silently
assumed by the present construction.

This adds no relation symbols or function values. It is
independent of all native set-valued function arities and
folded component predicates.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey

universe u

/-- A four-coordinate candidate order key for a target of a
finite amalgamation diagram. The final coordinate is the
canonical finite enumeration of the target, so distinct
target vertices always receive distinct keys.

The category branches deliberately prioritize the literal
shared-root image, then Y-side image, then Z-side image,
then any extra target vertices. Under the strong overlap
law the three categories have their intended meaning. -/
noncomputable def finiteAmalgamOrderKey
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (t : T) :
    Nat ×ₗ (Nat ×ₗ (Nat ×ₗ Fin (Fintype.card T))) := by
  classical
  exact
    if hroot : ∃ x : X, jY (sY x) = t then
      toLex (StructuralRamsey.Rooted.orderRank X
          (Classical.choose hroot),
        toLex ((2 : ℕ),
          toLex ((0 : ℕ), Fintype.equivFin T t)))
    else if hy : ∃ y : Y, jY y = t then
      toLex (finiteRootCutRank sY (Classical.choose hy),
        toLex ((0 : ℕ),
          toLex (StructuralRamsey.Rooted.orderRank Y
            (Classical.choose hy), Fintype.equivFin T t)))
    else if hz : ∃ z : Z, jZ z = t then
      toLex (finiteRootCutRank sZ (Classical.choose hz),
        toLex ((1 : ℕ),
          toLex (StructuralRamsey.Rooted.orderRank Z
            (Classical.choose hz), Fintype.equivFin T t)))
    else
      toLex ((Fintype.card X + 1 : ℕ),
        toLex ((3 : ℕ),
          toLex ((0 : ℕ), Fintype.equivFin T t)))

/-- The last coordinate of the target key is exactly the
chosen canonical enumeration of that original target vertex,
independent of which category branch was selected. -/
theorem finiteAmalgamOrderKey_last
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T)
    (t : T) :
    (ofLex (ofLex (ofLex
      (finiteAmalgamOrderKey sY sZ jY jZ t)).2).2).2 =
      Fintype.equivFin T t := by
  classical
  unfold finiteAmalgamOrderKey
  split_ifs <;> rfl

/-- The full four-coordinate key is always injective.
This requires no overlap or order hypotheses at all;
the final coordinate already distinguishes vertices. -/
theorem finiteAmalgamOrderKey_injective
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T) :
    Function.Injective (finiteAmalgamOrderKey sY sZ jY jZ) := by
  intro a b hab
  apply (Fintype.equivFin T).injective
  calc
    (Fintype.equivFin T) a =
        (ofLex (ofLex (ofLex
          (finiteAmalgamOrderKey sY sZ jY jZ a)).2).2).2 :=
      (finiteAmalgamOrderKey_last sY sZ jY jZ a).symm
    _ = (ofLex (ofLex (ofLex
          (finiteAmalgamOrderKey sY sZ jY jZ b)).2).2).2 :=
      congrArg
        (fun key : Nat ×ₗ (Nat ×ₗ (Nat ×ₗ Fin (Fintype.card T))) =>
          (ofLex (ofLex (ofLex key).2).2).2) hab
    _ = (Fintype.equivFin T) b :=
      finiteAmalgamOrderKey_last sY sZ jY jZ b

/-- A GENUINE linear order on the finite target carrier
constructed from the two finite ordered sides and their
chosen common-root placements. The next theorem must still
prove its compatibility with the side orders using the
exact strong-amalgamation overlap law. -/
noncomputable def finiteAmalgamLinearOrder
    {X Y Z T : Type}
    [Fintype X] [LinearOrder X]
    [Fintype Y] [LinearOrder Y]
    [Fintype Z] [LinearOrder Z]
    [Fintype T]
    (sY : X → Y) (sZ : X → Z)
    (jY : Y → T) (jZ : Z → T) : LinearOrder T :=
  LinearOrder.lift' (finiteAmalgamOrderKey sY sZ jY jZ)
    (finiteAmalgamOrderKey_injective sY sZ jY jZ)

end AllThoseRamseyClasses.Lifts
