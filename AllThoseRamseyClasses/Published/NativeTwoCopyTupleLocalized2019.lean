import AllThoseRamseyClasses.Published.NativeTwoTransverseCopyRoot2019
import AllThoseRamseyClasses.Published.NativeTwoActivePrivate2019

/-!
# A concrete two-copy transverse native K-completion from tuple localization

The CI-green two-copy A-root theorem #169 proves the shared vertex-exact
A-boundary and K-completion WHEN the exact source is already known
to be a free amalgam of two small sides inside distinct attached copies.
The free-amalgam premise is not automatic for a Hales--Jewett power:
a pure core relation can cross the exclusive portions of the two
line ranges (separate regression #170).

Here is an honest SOURCE-SPECIFIC sufficient criterion, phrased
directly on the original exact tested vertices and relation tuples.

Suppose an ordinary (possibly NONINJECTIVE) native projection p
of an exact weak source F to a true simultaneous attachment meets
ONLY attached copies i and j:
* each tested vertex maps into the range of at least one of
  those two full old-copy embeddings;
* each actual SOURCE RELATION TUPLE has ALL its projected vertices
  in the range of copy i OR ALL in copy j.
Then the exact inverse-image pieces L,R form a relational free
amalgam of F, with the literal intersection as root. This is
proved by the verified positive free-cover pullback applied to
identity on the ORIGINAL source, NOT by inventing a target
free-cover theorem on the full native power.

If the source actually visits each copy's private exterior,
both sides of the resulting split are PROPER. Under |F|<=rank+1,
each side has <=rank vertices. If the two HJ lines' parameter
sets are disjoint, their actual overlap factors through one
A-root by #169, and the old closed rank-j K-gluing criterion
completes the original source.

This is a real restricted native completion theorem with explicit
and testable source tuple-localization hypotheses. It does not
assert those hypotheses for arbitrary pure-core tuples, nor
solve higher-rank multi-line histories or corrected Theorem 2.18.
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

/-- The original exact maximal-rank weak source is completable when
its actual native projection is supported by two transverse copies,
EVERY source tuple localizes to one copy image, and the private
exterior of each copy is genuinely visited.

All source conditions are on the original vertex carrier and tuples.
No artificial closure hull, source-map injectivity or semiclosed
native target is assumed. -/
theorem native2019_two_copy_tuple_localized_weak_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V I U : Type v} {N : ℕ}
    [Fintype U] [Finite V] [Finite Q]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : System L P V)
    (alpha : Q ↪ P)
    (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i j : I) (hij : i ≠ j)
    (hTransverse : ∀ k : Fin N,
      (lines i).symbol k = .parameter →
      (lines j).symbol k ≠ .parameter)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (hVertices : ∀ x : U,
      InCopy Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) i (p x) ∨
      InCopy Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) j (p x))
    (hTuples : ∀ R (xs : Fin (L.arity R) → U),
      Source.rel R xs →
        (∀ k, InCopy Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)
          i (p (xs k))) ∨
        (∀ k, InCopy Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)
          j (p (xs k))))
    (hActiveI : ∃ x : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x))
    (hActiveJ : ∃ y : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p y))
    (rank : ℕ)
    (hTotal : Fintype.card U ≤ rank + 1)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {Z : Type v} (T : RelStructure L Z),
      K T → T.Irreducible)
    (hDClosed : IsUClosed rules Old.toRelStructure)
    (hAK : K A) (hAClosed : IsUClosed rules A)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ rank →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let LeftSet : Set U :=
    {x | InCopy Old.toRelStructure (Old.support alpha)
      Core maps i (p x)}
  let RightSet : Set U :=
    {x | InCopy Old.toRelStructure (Old.support alpha)
      Core maps j (p x)}
  have hId : Source.IsHomomorphism Source (fun x : U => x) := by
    intro R xs hxs
    exact hxs
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source LeftSet RightSet)
        (exactFreeCoverRootToRight Source LeftSet RightSet)
        (inclusion Source LeftSet)
        (inclusion Source RightSet) :=
    positive2019_pullback_exact_free_cover
      hId LeftSet RightSet hVertices hTuples
  let d : ProperFreeDecomposition Source := {
    Common := {x : U // x ∈ LeftSet ∩ RightSet}
    Left := LeftSet
    Right := RightSet
    common := Source.induce (LeftSet ∩ RightSet)
    left := Source.induce LeftSet
    right := Source.induce RightSet
    toLeft := exactFreeCoverRootToLeft Source LeftSet RightSet
    toRight := exactFreeCoverRootToRight Source LeftSet RightSet
    leftIn := inclusion Source LeftSet
    rightIn := inclusion Source RightSet
    free := hFree
    leftProper := by
      intro hSurj
      obtain ⟨y, hy⟩ := hActiveJ
      have hNot : ¬ InCopy Old.toRelStructure
          (Old.support alpha) Core maps i (p y) :=
        native2019_other_private_not_in_chosen_copy
          Old.toRelStructure (Old.support alpha)
          Core maps i j hij (p y) hy
      obtain ⟨x, hx⟩ := hSurj y
      change x.1 = y at hx
      exact hNot (hx ▸ x.2)
    rightProper := by
      intro hSurj
      obtain ⟨x, hx⟩ := hActiveI
      have hNot : ¬ InCopy Old.toRelStructure
          (Old.support alpha) Core maps j (p x) :=
        native2019_other_private_not_in_chosen_copy
          Old.toRelStructure (Old.support alpha)
          Core maps j i hij.symm (p x) hx
      obtain ⟨y, hy⟩ := hSurj x
      change y.1 = x at hy
      exact hNot (hy ▸ y.2)
  }
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hLessL : Fintype.card d.Left < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.leftIn d.leftIn.injective d.leftProper
  have hLessR : Fintype.card d.Right < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.rightIn d.rightIn.injective d.rightProper
  have hSmallL : Fintype.card d.Left ≤ rank := by omega
  have hSmallR : Fintype.card d.Right ≤ rank := by omega
  have hLeftRange (x : d.Left) :
      ∃ y : V, p (d.leftIn x) =
        copyMap Old.toRelStructure (Old.support alpha)
          Core maps i y := x.2
  have hRightRange (x : d.Right) :
      ∃ y : V, p (d.rightIn x) =
        copyMap Old.toRelStructure (Old.support alpha)
          Core maps j y := x.2
  exact native2019_two_transverse_copy_free_source_completion
    Old alpha A hRestricted lines i j hij hTransverse
    p hp hLeftRange hRightRange d.free hMax
    hStrong hHer hKIrr hDClosed hAK hAClosed
    rank hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
