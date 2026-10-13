import AllThoseRamseyClasses.Published.NativeTwoCopyTupleLocalized2019
import AllThoseRamseyClasses.Published.NativeClosedPictureWeakTrichotomy2019

/-!
# Paper-faithful two-copy native completion for exact tests of CLOSED Pictures

The CI-green real native two-copy tuple-localization theorem #172
requires an ORDINARY homomorphism-embedding of the tested weak source
into the actual simultaneous Hales--Jewett attachment.

The corrected 2019 iterated Picture Lemma 2.30 instead supplies a
PROTECTED U-homomorphism-embedding from a CLOSED FULL Picture C to
that attachment (it may itself be only temporarily closed/semi-closed).

Here the full source's U-closedness converts the corrected protected
map to an ordinary HE; restricting it to an arbitrary EXACT WEAK
induced test C|S supplies the ordinary input of #172. No closure
of S is postulated. The resulting theorem establishes a genuine
corrected K-completion for the original test whenever:

 * its own intrinsic U-size is its number of vertices (maximal),
 * all original test vertices project into two transverse copies,
 * each original test relation tuple is wholly localized to one
   of those two copy ranges,
 * each attached copy's private exterior is genuinely visited,
 * previous old closed rank-j tests have K-completions, with the
   original weak source having <=j+1 vertices.

The actual proper free cut, both bounded sides, two old-Picture
ordinary maps, and single vertex-exact A-letter root are now
CONSTRUCTED by the checked #172 / #169 native geometry.

The source tuple-localization requirement is NOT automatic,
because the native coordinate power can contain crossing core
relations (Lean regression #170). Nor does the statement
establish the much stronger original closed-generating-rank-j
increment, or treat 3+ active indices. Corrected Theorem 2.18
remains OPEN.
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

/-- Exact weak native two-copy completion from the ACTUAL protected
projection of a U-CLOSED full Picture. The tuple condition concerns
the source's original induced relation tuples, never the whole
power core or an invented closure hull. -/
theorem native2019_closed_picture_two_copy_tuple_localized_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V I VC : Type v} {N : ℕ}
    [Finite VC] [Finite V] [Finite Q]
    (C : RelStructure L VC)
    (hC : IsUClosed rules C)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i j : I) (hij : i ≠ j)
    (hTransverse : ∀ k : Fin N,
      (lines i).symbol k = .parameter →
      (lines j).symbol k ≠ .parameter)
    (p : VC → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules C
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (S : Finset VC)
    (hMax : USize rules (C.induce (↑S : Set VC)) = S.card)
    (hVertices : ∀ x : (↑S : Set VC),
      InCopy Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) i (p x.1) ∨
      InCopy Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) j (p x.1))
    (hTuples : ∀ R (xs : Fin (L.arity R) → (↑S : Set VC)),
      (C.induce (↑S : Set VC)).rel R xs →
        (∀ k, InCopy Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)
          i (p (xs k).1)) ∨
        (∀ k, InCopy Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines)
          j (p (xs k).1)))
    (hActiveI : ∃ x : (↑S : Set VC), OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x.1))
    (hActiveJ : ∃ y : (↑S : Set VC), OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p y.1))
    (rank : ℕ) (hCard : S.card ≤ rank + 1)
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
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set VC)) := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  have hpAbstract :
      IsClosedUHomomorphismEmbedding rules C
        (attach Old.toRelStructure (Old.support alpha) Core maps) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hpOrd :
      C.IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha) Core maps) p :=
    IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hpAbstract hC
  have hpTest :
      (C.induce (↑S : Set VC)).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha) Core maps)
        (fun x : (↑S : Set VC) => p x.1) :=
    hpOrd.comp (inclusion C (↑S : Set VC)).isHomomorphismEmbedding
  have hMaxCard :
      USize rules (C.induce (↑S : Set VC)) =
        Fintype.card (↑S : Set VC) := by
    simpa using hMax
  have hTotal : Fintype.card (↑S : Set VC) ≤ rank + 1 := by
    simpa using hCard
  exact native2019_two_copy_tuple_localized_weak_completion
    (C.induce (↑S : Set VC)) hMaxCard
    Old alpha A hRestricted lines i j hij hTransverse
    (fun x : (↑S : Set VC) => p x.1) hpTest
    hVertices hTuples hActiveI hActiveJ rank hTotal
    hStrong hHer hKIrr hDClosed hAK hAClosed hOldRank

end AllThoseRamseyClasses.Published
