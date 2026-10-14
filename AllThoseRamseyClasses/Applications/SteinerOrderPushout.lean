import AllThoseRamseyClasses.Applications.SteinerTripleClass
import AllThoseRamseyClasses.Applications.PosetAmalgamationOrder
import PartiteConstruction.Iterated.FreeAmalgam
import Mathlib.Order.Prod.Lex.Basic

/-!
# Extend freely ordered Steiner structures across genuine strong pushouts

Steiner systems use their OWN mixed-arity language with order, a binary
covered-pair relation and a ternary block relation. The already
checked ordered-poset amalgam keys use a different named binary
language; they cannot simply be applied to a Steiner free amalgam as
if its relation language were the poset language.

We transfer ONLY the vertex orders to a shadow of the checked
generic ordered-key construction, and independently glue the resulting
compatible keys across the genuine Steiner free amalgam. This yields
ONE linear order on exactly its vertices, restricting to the original
orders on each side. It imposes no convexity or relative ordering
condition on distinct private sides.

This lemma does not itself prove that the new complete relational
amalgam satisfies all block/covered-pair axioms. That final strong
amalgamation theorem is a separate application step.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.OrderedPosets

namespace Paired
open AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
end Paired

/-- A deliberately inert ordered shadow in the fixed three-binary
language used by the existing root-cut key construction. We never
claim that this shadow is a paired-equivalence structure. -/
def orderShadow {V : Type} (C : RelStructure Lang V) :
    RelStructure
      AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.Lang V where
  rel
    | .lt, t => C.rel .order t
    | .equiv, _ => False
    | .mate, _ => False

/-- Full embeddings of Steiner structures become full embeddings
of their named order shadows, including reflection of nonedges. -/
def orderShadowEmbedding {U V : Type}
    {A : RelStructure Lang U} {B : RelStructure Lang V}
    (e : Embedding A B) :
    Embedding (orderShadow A) (orderShadow B) where
  toFun := e
  injective := e.injective
  map_rel_iff := by
    intro R t
    cases R with
    | lt =>
      exact e.map_rel_iff .order t
    | equiv =>
      exact Iff.rfl
    | mate =>
      exact Iff.rfl

/-- The shadow is a finite ordinarily ordered ambient structure
using only the actual Steiner vertex order, no other axioms. -/
theorem orderShadow_ambient
    {V : Type} (C : RelStructure Lang V)
    (hC : orderedSteinerClass C) :
    AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.orderedAmbientClass
      (orderShadow C) :=
  ⟨hC.finite, hC.order_irrefl, hC.order_trans, hC.order_total⟩

/-- Compatible labels on a genuine strong Steiner free amalgam
extend to its whole carrier. This depends on the actual shared
vertex pushout, not merely on a weak union of relation tuples. -/
theorem steiner_freeAmalgam_compatible_label
    {D E F P Q : Type}
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E}
    {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (qL : E → Q) (qR : F → Q)
    (hCompat : ∀ d : D, qL (sL d) = qR (sR d)) :
    ∃ q : P → Q,
      (∀ a : E, q (iL a) = qL a) ∧
      (∀ b : F, q (iR b) = qR b) := by
  classical
  let Represents (z : P) (w : Q) : Prop :=
    (∃ a : E, z = iL a ∧ w = qL a) ∨
    (∃ b : F, z = iR b ∧ w = qR b)
  have hUnique (z : P) : ∃! w : Q, Represents z w := by
    obtain ⟨a, ha⟩ | ⟨b, hb⟩ := hFree.covers z
    · refine ⟨qL a, Or.inl ⟨a, ha, rfl⟩, ?_⟩
      intro w hw
      rcases hw with ⟨a', ha', rfl⟩ | ⟨b, hb, rfl⟩
      · have he : a = a' := iL.injective (ha.symm.trans ha')
        subst a'
        rfl
      · obtain ⟨d, haD, hbD⟩ :=
          (hFree.overlap a b).mp (ha.symm.trans hb)
        subst a
        subst b
        exact (hCompat d).symm
    · refine ⟨qR b, Or.inr ⟨b, hb, rfl⟩, ?_⟩
      intro w hw
      rcases hw with ⟨a, ha, rfl⟩ | ⟨b', hb', rfl⟩
      · obtain ⟨d, haD, hbD⟩ :=
          (hFree.overlap a b).mp (ha.symm.trans hb)
        subst a
        subst b
        exact hCompat d
      · have he : b = b' := iR.injective (hb.symm.trans hb')
        subst b'
        rfl
  let q : P → Q := fun z => Classical.choose (hUnique z)
  refine ⟨q, ?_, ?_⟩
  · intro a
    have h : Represents (iL a) (qL a) :=
      Or.inl ⟨a, rfl, rfl⟩
    exact ((Classical.choose_spec (hUnique (iL a))).2 (qL a) h).symm
  · intro b
    have h : Represents (iR b) (qR b) :=
      Or.inr ⟨b, rfl, rfl⟩
    exact ((Classical.choose_spec (hUnique (iR b))).2 (qR b) h).symm

/-- A strong free amalgam of any two well-formed ordered partial
Steiner triple systems over a common full subsystem admits a SINGLE
strict linear order extending both complete original vertex orders.
The order lives on the original strong union: no additional points
are identified. -/
theorem steiner_freeAmalgam_order_extension
    {D E F P : Type}
    [Finite D] [Finite E] [Finite F] [Finite P]
    {Root : RelStructure Lang D}
    {Left : RelStructure Lang E}
    {Right : RelStructure Lang F}
    {Whole : RelStructure Lang P}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : orderedSteinerClass Left)
    (hRight : orderedSteinerClass Right) :
    ∃ (o : LinearOrder P),
      (∀ a b : E, edge Left .order a b →
        @LT.lt P o.toLT (iL a) (iL b)) ∧
      (∀ a b : F, edge Right .order a b →
        @LT.lt P o.toLT (iR a) (iR b)) := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype F := Fintype.ofFinite F
  let eL := orderShadowEmbedding sL
  let eR := orderShadowEmbedding sR
  let keyL : E → ℕ ×ₗ (ℕ ×ₗ ℕ) :=
    AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.sideOrderKey
      (orderShadow Left) eL 0
  let keyR : F → ℕ ×ₗ (ℕ ×ₗ ℕ) :=
    AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.sideOrderKey
      (orderShadow Right) eR 1
  have hCompat : ∀ d : D, keyL (sL d) = keyR (sR d) :=
    AllThoseRamseyClasses.Published.PairedEquivalenceObstruction.sideOrderKey_root_agree
      eL eR
  have hLtL : ∀ a b : E, edge Left .order a b →
      keyL a < keyL b := by
    intro a b hab
    exact ambient_sideOrderKey_strictMono (orderShadow Left)
      (orderShadow_ambient Left hLeft) eL 0 (by omega) hab
  have hLtR : ∀ a b : F, edge Right .order a b →
      keyR a < keyR b := by
    intro a b hab
    exact ambient_sideOrderKey_strictMono (orderShadow Right)
      (orderShadow_ambient Right hRight) eR 1 (by omega) hab
  obtain ⟨q, hL, hR⟩ :=
    steiner_freeAmalgam_compatible_label hFree keyL keyR hCompat
  letI : Fintype P := Fintype.ofFinite P
  let key : P → (ℕ ×ₗ (ℕ ×ₗ ℕ)) ×ₗ Fin (Fintype.card P) :=
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

end AllThoseRamseyClasses.Applications.SteinerTriples
