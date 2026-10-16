import PartiteConstruction.Functional.WeakOperations
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Changing one side of a FULL functional free amalgam by isomorphism

A geometric forbidden piece often appears only up to a full rooted
isomorphism, whereas its complement is embedded in the ORIGINAL
forbidden source. Replacing one free-amalgam side by an isomorphic
copy must preserve the exact full functional diagram, not only its
Gaifman graph.

We first construct a FULL inverse to a surjective full embedding,
using the verified closed embedding factorization API. Its inverse
preserves and reflects complete function fibres.

The side-transport theorem then preserves the four fields of
`Structure.IsFreeAmalgam`: carrier coverage, exact intersection,
positive relation tuple localization, and positive function
input/output incidences. It neither changes the forbidden-source
carrier nor introduces extra function values.

This is reusable in the selected-forbidden-piece nonempty-profile
proof and in global root-chart normalization of the 2019 lift.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v

/-- Inverse of a surjective FULL native functional embedding.
The inverse is itself full, unlike inverse maps of weak homomorphisms. -/
noncomputable def inverseFullEmbedding
    {L : Language.{u}}
    {U V : Type v} {A : Structure L U} {B : Structure L V}
    (e : Structure.Embedding A B)
    (he : Function.Surjective e) :
    Structure.Embedding B A :=
  (Structure.Embedding.id B).factorWithMap
    e (fun b => Classical.choose (he b))
    (fun b => (Classical.choose_spec (he b)).symm)

/-- The inverse cancels the original map on the entire target. -/
@[simp] theorem inverseFullEmbedding_right
    {L : Language.{u}}
    {U V : Type v} {A : Structure L U} {B : Structure L V}
    (e : Structure.Embedding A B)
    (he : Function.Surjective e) (b : V) :
    e (inverseFullEmbedding e he b) = b := by
  exact Classical.choose_spec (he b)

/-- The inverse also cancels the original map on every source
vertex, by injectivity of the original full embedding. -/
@[simp] theorem inverseFullEmbedding_left
    {L : Language.{u}}
    {U V : Type v} {A : Structure L U} {B : Structure L V}
    (e : Structure.Embedding A B)
    (he : Function.Surjective e) (a : U) :
    inverseFullEmbedding e he (e a) = a :=
  e.injective (inverseFullEmbedding_right e he (e a))

/-- Replace the left-hand side of any full functional free-amalgam
diagram by an onto, FULLY isomorphic copy, preserving the original
whole source and the other free-amalgam side. -/
theorem freeAmalgam_precompose_left_iso
    {L : Language.{u}}
    {H E E' F W : Type v}
    {Root : Structure L H}
    {Left : Structure L E}
    {NewLeft : Structure L E'}
    {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (e : Structure.Embedding NewLeft Left)
    (he : Function.Surjective e)
    (sNew : Structure.Embedding Root NewLeft)
    (hroot : ∀ r : H, e (sNew r) = sL r) :
    Structure.IsFreeAmalgam sNew sR (iL.comp e) iR := by
  classical
  let g : Structure.Embedding Left NewLeft :=
    inverseFullEmbedding e he
  have heg (a : E) : e (g a) = a :=
    inverseFullEmbedding_right e he a
  have hge (a : E') : g (e a) = a :=
    inverseFullEmbedding_left e he a
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    rcases hfree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
    · left
      refine ⟨g a, ?_⟩
      calc
        z = iL a := ha
        _ = iL (e (g a)) := congrArg iL (heg a).symm
        _ = (iL.comp e) (g a) := rfl
    · exact Or.inr ⟨b, hb⟩
  · intro a b
    constructor
    · intro hab
      obtain ⟨r, hrL, hrR⟩ :=
        (hfree.overlap (e a) b).mp hab
      refine ⟨r, ?_, hrR⟩
      apply e.injective
      calc
        e a = sL r := hrL
        _ = e (sNew r) := (hroot r).symm
    · rintro ⟨r, ha, hb⟩
      apply (hfree.overlap (e a) b).mpr
      refine ⟨r, ?_, hb⟩
      rw [ha]
      exact hroot r
  · intro R xs
    constructor
    · intro hxs
      rcases (hfree.rel_iff R xs).mp hxs with
        ⟨as, has, hargs⟩ | ⟨bs, hbs, hargs⟩
      · let asNew : Fin (L.relArity R) → E' := g ∘ as
        have hnew : NewLeft.rel R asNew :=
          (g.map_rel_iff R as).mpr has
        have hmap :
            ((iL.comp e) ∘ asNew) = iL ∘ as := by
          funext i
          exact congrArg iL (heg (as i))
        exact Or.inl ⟨asNew, hnew, hargs.trans hmap.symm⟩
      · exact Or.inr ⟨bs, hbs, hargs⟩
    · rintro (⟨as, has, hargs⟩ | ⟨bs, hbs, hargs⟩)
      · apply (hfree.rel_iff R xs).mpr
        refine Or.inl ⟨e ∘ as, (e.map_rel_iff R as).mpr has, ?_⟩
        simpa [Function.comp_assoc] using hargs
      · exact (hfree.rel_iff R xs).mpr (Or.inr ⟨bs, hbs, hargs⟩)
  · intro F xs y
    constructor
    · intro hy
      rcases (hfree.func_iff F xs y).mp hy with
        ⟨as, a, ha, hargs, hout⟩ |
        ⟨bs, b, hb, hargs, hout⟩
      · let asNew : Fin (L.funcArity F) → E' := g ∘ as
        have hnew : g a ∈ NewLeft.func F asNew := by
          rw [g.map_func F as]
          exact ⟨a, ha, rfl⟩
        have hmap :
            ((iL.comp e) ∘ asNew) = iL ∘ as := by
          funext i
          exact congrArg iL (heg (as i))
        refine Or.inl ⟨asNew, g a, hnew, ?_, ?_⟩
        · exact hargs.trans hmap.symm
        · calc
            y = iL a := hout
            _ = iL (e (g a)) := congrArg iL (heg a).symm
            _ = (iL.comp e) (g a) := rfl
      · exact Or.inr ⟨bs, b, hb, hargs, hout⟩
    · rintro (⟨as, a, ha, hargs, hout⟩ |
              ⟨bs, b, hb, hargs, hout⟩)
      · have heval : e a ∈ Left.func F (e ∘ as) := by
          rw [e.map_func F as]
          exact ⟨a, ha, rfl⟩
        apply (hfree.func_iff F xs y).mpr
        refine Or.inl ⟨e ∘ as, e a, heval, ?_, ?_⟩
        · simpa [Function.comp_assoc] using hargs
        · exact hout
      · exact (hfree.func_iff F xs y).mpr
          (Or.inr ⟨bs, b, hb, hargs, hout⟩)

end AllThoseRamseyClasses.Lifts
