import AllThoseRamseyClasses.Published.EquivalencePushoutLabels
import Mathlib.Order.Prod.Lex.Basic

/-!
# Global finite linear order from compatible strict side keys

The proof separates the generic order-extension mechanism from
the particular root-cut keys used for paired equivalences.

Assume a genuine strong vertex pushout and two maps from its sides
into ONE linearly ordered label set. If those maps agree on the root
and strictly respect the two existing side orders, the labels
glue to one global map. Adding an arbitrary unique finite
tie-breaker makes it injective; lifting the lexicographic linear
order then extends BOTH original strict orders simultaneously.

No extra hypothesis about convexity of equivalence classes
or a linear extension oracle is needed. This is a verified
order-embedding conclusion only, not a complete strong amalgam.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- A strong pushout of finite ordered structures has a common
linear order whenever strict side-order preserving keys agree
on the identified root. -/
theorem IsFreeAmalgam.exists_order_from_compatible_keys
    {D E F P Q : Type}
    [Finite P] [LinearOrder Q]
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E}
    {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (qL : E → Q) (qR : F → Q)
    (hCompat : ∀ d : D, qL (sL d) = qR (sR d))
    (hLtL : ∀ a b : E, edge Left .lt a b → qL a < qL b)
    (hLtR : ∀ a b : F, edge Right .lt a b → qR a < qR b) :
    ∃ o : LinearOrder P,
      (∀ a b : E, edge Left .lt a b →
        @LT.lt P o.toLT (iL a) (iL b)) ∧
      (∀ a b : F, edge Right .lt a b →
        @LT.lt P o.toLT (iR a) (iR b)) := by
  classical
  obtain ⟨q, hL, hR⟩ :=
    IsFreeAmalgam.exists_compatible_label hFree qL qR hCompat
  letI : Fintype P := Fintype.ofFinite P
  let key : P → Q ×ₗ Fin (Fintype.card P) :=
    fun z => toLex (q z, Fintype.equivFin P z)
  have hKeyInj : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin P).injective
    exact congrArg (fun z => (ofLex z).2) hxy
  let o : LinearOrder P := LinearOrder.lift' key hKeyInj
  refine ⟨o, ?_, ?_⟩
  · intro a b hab
    change key (iL a) < key (iL b)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    simpa only [hL a, hL b] using hLtL a b hab
  · intro a b hab
    change key (iR a) < key (iR b)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    simpa only [hR a, hR b] using hLtR a b hab

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
