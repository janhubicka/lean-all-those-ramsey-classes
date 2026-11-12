import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureClosedMap

/-!
# Track C: exact-image transfer of genuine H-relative OLD weak completions

English-first proof route: a second native B-cover pass could be used
after the verified two-pass OLD witness, if its weak projection into
the first witness can be lifted to an induced-closed OLD U-homomorphism
embedding on the exact source and target carriers.

This lemma verifies the categorical core of that route. Its hypothesis
is a *genuine tagged protected* map, not merely a source-defined
positive functional map or an EHN map whose tagged lift is unknown.
That remaining source-geometry/encoding bridge is separate.

At the ORIGINAL n-vertex cutoff, the image of any finite source D
with at most n vertices has at most n vertices. Complete this
exact ambient weak image in the old candidate; restrict the
codomain of the protected control map to this image; compose
with the H-valued local completion. Neither source is replaced
by a U-closure hull. Some-empty, source OLD domain masks and
protected closed U-irreducible tests are retained by the
induced-closed map condition.

No reducible-root gluing or generating-rank hypothesis is used.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {X V : Type w}

/-- A protected OLD map into a candidate with all n-small exact weak
H completions transfers an H completion to any source of at most n
original vertices, even if that source is not U-closed.

The image is the literal Finset image; the H target can depend on
that image, and the composite vertex map is unchanged. -/
theorem genuineTagged2019_relativeCompletion_of_protectedSmallImage
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    [Finite V]
    (n : ℕ)
    (hSmall : ∀ (S : Finset V), S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set V)))
    (D : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    [Finite X]
    (p : X → V)
    (hp : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      D C p)
    (hCard : Nat.card X ≤ n) :
    HasGenuinePartiteTagged2019RelativeCompletion H D := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let S : Finset V := Finset.univ.image p
  have hSCard : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset X).card := Finset.card_image_le
      _ = Fintype.card X := Finset.card_univ
      _ = Nat.card X := by rw [Nat.card_eq_fintype_card]
      _ ≤ n := hCard
  let pS : X → (↑S : Set V) :=
    fun x => ⟨p x, Finset.mem_image.mpr
      ⟨x, Finset.mem_univ x, rfl⟩⟩
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hpS : IsInducedClosedUHomomorphismEmbedding
      rules D (C.induce (↑S : Set V)) pS :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      ((IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp).codRestrict
        (↑S : Set V)
        (fun x => Finset.mem_image.mpr
          ⟨x, Finset.mem_univ x, rfl⟩))
  obtain ⟨Y, hY, Target, targetPart, hH, hTr, hIrred, f, hf⟩ :=
    hSmall S hSCard
  have hComp : IsInducedClosedUHomomorphismEmbedding
      rules D
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart))
      (f ∘ pS) :=
    inducedClosedMap_comp_2019 hf hpS
  exact ⟨Y, hY, Target, targetPart, hH, hTr, hIrred,
    f ∘ pS, hComp⟩

end AllThoseRamseyClasses.Published
