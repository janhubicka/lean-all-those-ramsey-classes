import AllThoseRamseyClasses.Applications.PosetAmalgamationOrder
import PartiteConstruction.Iterated.FreeAmalgam

/-!
# Explicit partial-order amalgamation over a full common root

The strict-total-order amalgam is already verified. The outstanding
poset property is independent REFLECTION of the partial order on
both old sides: naïve free relational amalgamation need not be
transitive, while naïve completion by transitive closure must
not add new comparisons inside either side.

On the genuine strong FREE vertex pushout, record a comparison:
* inside one side, use that side's original partial order;
* across sides, demand a witness in the SAME induced root that
  lies between the two vertices in their respective side orders.

The crossing-root witness makes transitivity a short 8-case proof.
No use of category theory, additional identifications, the disputed
old generating-rank lemma, or stronger root assumptions.

This component asserts neither the existence of a compatible linear
order nor the final K-strong amalgamation theorem. Both are separate
from the verified reflexive/transitive algebra proved here.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- A comparison across the two sides of a strong vertex pushout
must factor through ONE actual vertex of the shared induced root.
For same-side pairs the relation is exactly the old relation. -/
def posetPushoutRelation
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (pL : E → E → Prop) (pR : F → F → Prop) :
    FreeAmalgam.Vertex Root Left Right sL sR →
    FreeAmalgam.Vertex Root Left Right sL sR → Prop :=
  fun x y =>
    match x, y with
    | .inl a, .inl b => pL a b
    | .inl a, .inr (_, b) =>
      ∃ d : H, pL a (sL d) ∧ pR (sR d) b.1
    | .inr (_, a), .inl b =>
      ∃ d : H, pR a.1 (sR d) ∧ pL (sL d) b
    | .inr (_, a), .inr (_, b) => pR a.1 b.1

/-- The pushout relation is reflexive whenever the two original
partial orders are reflexive; no properties of their cross orders
are used. -/
theorem posetPushoutRelation_refl
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (pL : E → E → Prop) (pR : F → F → Prop)
    (hL : ∀ x : E, pL x x)
    (hR : ∀ x : F, pR x x) :
    ∀ x : FreeAmalgam.Vertex Root Left Right sL sR,
      posetPushoutRelation Root Left Right sL sR pL pR x x := by
  intro x
  rcases x with x | ⟨_, x⟩
  · exact hL x
  · exact hR x.1

/-- Root reflection means that the two induced side relations
agree on ALL root pairs, including absent positive pairs. -/
theorem posetPushoutRelation_trans
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (pL : E → E → Prop) (pR : F → F → Prop)
    (hL : ∀ x y z : E, pL x y → pL y z → pL x z)
    (hR : ∀ x y z : F, pR x y → pR y z → pR x z)
    (hRoot : ∀ d e : H,
      pL (sL d) (sL e) ↔ pR (sR d) (sR e)) :
    ∀ x y z : FreeAmalgam.Vertex Root Left Right sL sR,
      posetPushoutRelation Root Left Right sL sR pL pR x y →
      posetPushoutRelation Root Left Right sL sR pL pR y z →
      posetPushoutRelation Root Left Right sL sR pL pR x z := by
  intro x y z hxy hyz
  rcases x with a | ⟨_, a⟩ <;>
    rcases y with b | ⟨_, b⟩ <;>
    rcases z with c | ⟨_, c⟩
  all_goals dsimp only [posetPushoutRelation] at *
  · exact hL a b c hxy hyz
  · rcases hyz with ⟨d, hbd, hdc⟩
    exact ⟨d, hL a b (sL d) hxy hbd, hdc⟩
  · rcases hxy with ⟨d, had, hdb⟩
    rcases hyz with ⟨e, hbe, hec⟩
    have hde : pL (sL d) (sL e) :=
      (hRoot d e).mpr (hR (sR d) b.1 (sR e) hdb hbe)
    exact hL a (sL d) c had
      (hL (sL d) (sL e) c hde hec)
  · rcases hxy with ⟨d, had, hdb⟩
    exact ⟨d, had, hR (sR d) b.1 c.1 hdb hyz⟩
  · rcases hxy with ⟨d, had, hdb⟩
    exact ⟨d, had, hL (sL d) b c hdb hyz⟩
  · rcases hxy with ⟨d, had, hdb⟩
    rcases hyz with ⟨e, hbe, hec⟩
    have hde : pR (sR d) (sR e) :=
      (hRoot d e).mp (hL (sL d) b (sL e) hdb hbe)
    exact hR a.1 (sR d) c.1 had
      (hR (sR d) (sR e) c.1 hde hec)
  · rcases hyz with ⟨d, hbd, hdc⟩
    exact ⟨d, hR a.1 b.1 (sR d) hxy hbd, hdc⟩
  · exact hR a.1 b.1 c.1 hxy hyz

/-- Left/left reflection is definitional, independent of
how the two sides are later order-completed. -/
theorem posetPushoutRelation_left_iff
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (pL : E → E → Prop) (pR : F → F → Prop)
    (a b : E) :
    posetPushoutRelation Root Left Right sL sR pL pR
        (FreeAmalgam.leftEmbedding Root Left Right sL sR a)
        (FreeAmalgam.leftEmbedding Root Left Right sL sR b) ↔
      pL a b := by
  rfl

end AllThoseRamseyClasses.Applications.OrderedPosets
