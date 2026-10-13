import AllThoseRamseyClasses.Published.NativeTwoRestRootCardinality2019
import AllThoseRamseyClasses.Published.NativeTwoRestClosedKRootCompletion2019
import AllThoseRamseyClasses.Published.ClosedMaximalIrreducibleKRoot2019

/-!
# A genuine CLOSED three-vertex two-REST source completes over its literal K-root

This is a sharp small-case consequence of the true native multi-attachment
geometry.  Under two distinct private-active copy indices i,j, the common
source root of their two complementary RESTs omits two distinct original
source vertices.  Hence any original source with <=3 vertices has a common
root with <=1 vertex, automatically ordinary irreducible.

Assume in addition the whole original finite source is INTRINSICALLY
U-CLOSED and its intrinsic USize equals its number of vertices.
Then every induced source subset, including that literal common root,
is U-CLOSED.  If the whole source satisfies the original closed
U-irreducible B-copy coverage, that irreducible root is a genuine
member of K by closed heredity.

The previously VERIFIED native two-REST lemma with a closed K-root
then completes the ORIGINAL three-vertex source using the old closed
rank-two invariant.  All tuple-crossing pure-core relations are
handled by the genuine complementary REST free cover, not by
the false claim that two transverse COPY images form a free cover.

Restrictions are ESSENTIAL: the whole source must be U-closed and
maximal rank, the only active private copy indices are i,j, both
private exteriors must be visited, and the old closed rank-two
invariant must be available.  An arbitrary nonclosed weak source
is not covered by this result.  Nor does it establish the
general higher-rank Lemma 2.30 or Theorem 2.18.
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

/-- The two-active-line native rank-three special case:

* original exact source is U-CLOSED and has maximal intrinsic USize;
* its vertex set has at most THREE elements;
* it has the original closed U-irreducible B-copy coverage and closed
  hereditary K;
* both private exterior indices i,j occur and no other index occurs;
* Old satisfies closed-rank-TWO K-completion.

Then the WHOLE original source has a corrected K-completion.
The root-K premise of the general two-REST theorem is CONSTRUCTED
from ordinary irreducibility of its <=1-vertex exact common root. -/
theorem native2019_closed_maximal_three_vertex_two_rest_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U UB I : Type v} {N : ℕ}
    [Fintype U] [Finite V]
    (Source : RelStructure L U)
    (hSourceClosed : IsUClosed rules Source)
    (hMax : USize rules Source = Fintype.card U)
    (B : RelStructure L UB)
    (hBK : K B)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test Source →
      Nonempty (Embedding Test B))
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
    (hCard : Fintype.card U ≤ 3)
    (hOldClosed : IsUClosed rules Old.toRelStructure)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (S : RelStructure L X),
      K S → S.Irreducible)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ 2 →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let Root : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x) ∧
      ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  have hRootIrred : (Source.induce Root).Irreducible :=
    native2019_two_rest_small_root_irreducible Source
      (Old.support alpha) p i j hij hActiveI hActiveJ hCard
  obtain ⟨hRootClosed, hRootK⟩ :=
    native2019_closed_maximal_irreducible_root_is_K
      Source B hSourceClosed hMax hBK hHer hCover
      Root hRootIrred
  have hRootSet :
      Root =
      ({x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x)} ∩
       {x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)}) := by
    ext x
    rfl
  rw [hRootSet] at hRootClosed hRootK
  exact native2019_two_rest_complete_of_literal_closed_K_root
    Source hMax Old alpha A hRestricted lines p hp
    i j hij hOnly hActiveI hActiveJ
    hRootK hRootClosed 2 hCard
    hOldClosed hStrong hHer hKIrr hOldRank

end AllThoseRamseyClasses.Published
