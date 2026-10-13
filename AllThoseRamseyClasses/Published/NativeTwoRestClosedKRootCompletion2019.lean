import AllThoseRamseyClasses.Published.NativeTwoRestFree2019
import AllThoseRamseyClasses.Published.NativeTwoActiveRestOrdinary2019
import AllThoseRamseyClasses.Published.ClosedKRootTwoSide2019

/-!
# Actual native two-REST K-completion when its literal separator IS a closed K-root

In the genuine two-active-copy native Hales--Jewett attachment,
the two complementary REST subsets always give a relational free
cover of the ORIGINAL weak source; pure power-core crossing tuples
lie in BOTH rests. Under the only-i,j-active hypothesis, each REST
has its own genuine HJ parameter coordinate and therefore admits
an ORDINARY old-Picture homomorphism-embedding.

A restricted but rigorous completion follows when the LITERAL
source separator (intersection of these exact REST preimages)
is already U-CLOSED and belongs to K. K-members are ordinarily
irreducible, so the two old-side ordinary maps restrict to FULL
embeddings of that SAME K-root in the old closed Picture. The
checked old closed-rank-j two-side gluing lemma finishes the
ORIGINAL maximal-intrinsic-rank weak source, with no fixed
A-letter root assumption and no relation tuple localization
to the generally nonfree two HJ COPY ranges.

The root-Uclosed/root-K premise is explicit and NOT implied by
the existing possibly NONINJECTIVE protected core-root completion
into A. Nor does properness of weak sides establish closed-rank
bounds for arbitrary closed tests of many vertices.
No unrestricted Lemma 2.30 or Theorem 2.18 is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- Under the exact two-source-active native hypothesis, a maximal
U-rank weak test on at most r+1 ORIGINAL vertices is completable
when the literal entire two-REST common source root already is a
U-CLOSED K-member. The root need NOT lie in one fixed A-letter
word; the compatible embeddings come from its own K-irreducibility.

The old closed rank-r invariant is a real premise. Ordinary
W_r of small weak old sets is NOT substituted for it. -/
theorem native2019_two_rest_complete_of_literal_closed_K_root
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Fintype U] [Finite V]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (i j : I) (hij : i ≠ j)
    (hOnly : ∀ k : I,
      (∃ x : U, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x)) →
        k = i ∨ k = j)
    (hActiveI : ∃ x : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x))
    (hActiveJ : ∃ y : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p y))
    (hRootK : K (Source.induce
      ({x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x)} ∩
       {x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)})))
    (hRootClosed : IsUClosed rules (Source.induce
      ({x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x)} ∩
       {x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)})))
    (r : ℕ) (hCard : Fintype.card U ≤ r+1)
    (hOldClosed : IsUClosed rules Old.toRelStructure)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (S : RelStructure L X),
      K S → S.Irreducible)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ r →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let S := Old.support alpha
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let LeftSet : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) S j (p x)}
  let RightSet : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) S i (p x)}
  letI : Finite LeftSet :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite RightSet :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (LeftSet ∩ RightSet) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype LeftSet := Fintype.ofFinite LeftSet
  letI : Fintype RightSet := Fintype.ofFinite RightSet
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source LeftSet RightSet)
        (exactFreeCoverRootToRight Source LeftSet RightSet)
        (inclusion Source LeftSet) (inclusion Source RightSet) :=
    native2019_positive_two_rest_source_free
      Source Old.toRelStructure S Core maps p hp.1 i j hij
  obtain ⟨fL, fR, hfL, hfR⟩ :=
    native2019_two_only_active_rest_ordinary_old_maps
      Source Old alpha A hRestricted lines p hp i j hij hOnly
  have hLeftProper :
      ¬ Function.Surjective (inclusion Source LeftSet) := by
    intro hSurj
    obtain ⟨x, hx⟩ := hActiveJ
    obtain ⟨y, hy⟩ := hSurj x
    change y.1 = x at hy
    exact (hy ▸ y.2) hx
  have hRightProper :
      ¬ Function.Surjective (inclusion Source RightSet) := by
    intro hSurj
    obtain ⟨x, hx⟩ := hActiveI
    obtain ⟨y, hy⟩ := hSurj x
    change y.1 = x at hy
    exact (hy ▸ y.2) hx
  have hLessL : Fintype.card LeftSet < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      (inclusion Source LeftSet)
      (inclusion Source LeftSet).injective hLeftProper
  have hLessR : Fintype.card RightSet < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      (inclusion Source RightSet)
      (inclusion Source RightSet).injective hRightProper
  have hSmallL : Fintype.card LeftSet ≤ r := by omega
  have hSmallR : Fintype.card RightSet ≤ r := by omega
  exact inducedClosed2019_maximal_weak_two_old_maps_glue_of_closed_K_root
    hFree hMax Old.toRelStructure hOldClosed
    hStrong hHer hKIrr hRootK hRootClosed
    fL fR hfL hfR r hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
