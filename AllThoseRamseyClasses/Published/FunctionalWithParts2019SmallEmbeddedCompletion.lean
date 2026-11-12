import AllThoseRamseyClasses.Published.FunctionalWithParts2019GeneratedClosedTests
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# Track C: rank-j completion of ANY embedded small weak source

The merged corrected 2019 closed U-rank-j test invariant already
completes all ambient exact weak induced S with |S|<=j.
A source D with <=j vertices may have a DIFFERENT vertex type,
but if there is a full relational embedding e : D -> C, it is
isomorphic to the exact induced structure on its range in C.

The range is a Finset of at most |D| vertices. Complete that
exact induced range using the checked rank bridge, then pull
the protected completion back along the FULL embedding.
The target genuine H-member is unchanged; the final map is
the original relative map precomposed with the range inclusion.

No function closure is generated and no NEW source vertices appear.
The OLD independent domain-mask records are reflected wherever the
source full embedding reflects them. This is the transport needed
to instantiate lower-rank induction on the sides of a free weak cut.

This does NOT imply the published closed VERTEX-size local class
hypothesis supplies the rank-j premise; that remains separate.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- The verified rank-j closed-test completion invariant supplies
an actual genuine H-relative completion of ANY full embedded
weak source D with <=j vertices. The vertex carrier D is
unchanged, not replaced by its ambient generated closure. -/
theorem genuineTagged2019_embeddedWeakSmall_of_closedRank
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (j : ℕ)
    (hRank : ∀ (T : Set V) [Fintype T],
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) →
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce T) ≤ j →
      HasGenuinePartiteTagged2019RelativeCompletion H (C.induce T))
    {X : Type w} [Finite X]
    (D : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (e : RelStructure.Embedding D C)
    (hCard : Nat.card X ≤ j) :
    HasGenuinePartiteTagged2019RelativeCompletion H D := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let S : Finset V := Finset.univ.image e.toFun
  have hSize : S.card ≤ j := by
    calc
      S.card ≤ (Finset.univ : Finset X).card := Finset.card_image_le
      _ = Fintype.card X := Finset.card_univ
      _ = Nat.card X := by rw [Nat.card_eq_fintype_card]
      _ ≤ j := hCard
  let incl : RelStructure.Embedding D (C.induce (↑S : Set V)) := {
    toFun := fun x => ⟨e x, by
      change e x ∈ S
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ x, rfl⟩⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R xs
      change C.rel R (e.toFun ∘ xs) ↔ D.rel R xs
      exact e.map_rel_iff R xs
  }
  have hSmall :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set V)) :=
    (genuineTagged2019_allSmallWeak_of_closedUSize
      H C hClosed j hRank) S hSize
  obtain ⟨Y, hY, Target, targetPart, hTargetH, hTr, hIrred, f, hf⟩ :=
    hSmall
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hPull :
      IsInducedClosedUHomomorphismEmbedding
        rules D
        (wholeMaskTagExpansion
          (withPartsWholeMaskOld Target targetPart))
        (f ∘ incl.toFun) :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      ((IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf)
        .precomp_embedding incl)
  exact ⟨Y, hY, Target, targetPart, hTargetH, hTr, hIrred,
    f ∘ incl.toFun, hPull⟩

end AllThoseRamseyClasses.Published
