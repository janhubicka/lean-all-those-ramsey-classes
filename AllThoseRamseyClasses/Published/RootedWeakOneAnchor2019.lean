import AllThoseRamseyClasses.Published.RootedWeakSizeBase2019
import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide

/-!
# A SINGLE A-ANCHORED source vertex turns rooted W_j^A into W_(j+1)

The corrected 2019 weak-size iteration retains completions of original
weak j-vertex tests. The earlier full-A-within-j-weak-image strategy is
impossible whenever |A|>j. Our stronger rooted W_j^A avoids that by
providing a prescribed full embedded A-copy *in addition* to the j
extra old vertices.

A useful direct completion principle follows:
If an arbitrary finite EXACT weak source on at most j+1 vertices admits
a corrected PROTECTED map to Old, and the image of just ONE source vertex
lies in SOME genuine full A-copy of Old, then the entire original weak
source has a corrected K-completion from W_j^A(Old).

Indeed, choose one such anchored vertex x and charge the projected
images of ALL OTHER source vertices to the weak j-vertex allowance.
Their image has at most j vertices. The full image of Source lies in
T U a[A], where T is that image of the other source vertices. Complete
the exact induced Old test T U a[A] by W_j^A, and pull the completion
back along the ORIGINAL protected weak source map. No whole-source
injectivity, closedness, maximal U-size, or U-closure hull is required.

We separately instantiate this for an ORDINARY Old map from a MAXIMAL
U-rank weak source, using the checked automatic protectedness.
This may resolve the common-coordinate noncolliding branch IF the
actual Hales--Jewett history can supply even one source vertex in
an embedded A-copy. That root-HIT assertion is an explicit geometric
hypothesis, NOT silently assumed or universally established here.

No native rooted j->j+1 Picture constructor or repaired Theorem 2.18
is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A single actual A-anchored vertex in the image of a corrected
protected map suffices to complete the whole weak source with
<=j+1 vertices, using only the ROOTED W_j^A old invariant.

One anchored x is not charged against the j weak vertices: all
other vertices form a set of size <=j, and their OLD images form
the required finite weak target support T. -/
theorem inducedClosed2019_weaksize_completion_of_one_A_anchor
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U V P : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (A : RelStructure L P)
    (f : U → V)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source Old f)
    (j : ℕ) (hCard : Fintype.card U ≤ j+1)
    (a : Embedding A Old)
    (x : U) (hAnchor : f x ∈ Set.range a)
    (hRooted : Has2019RootedWeakSizeCompletions K rules Old A j) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let G : Finset U := (Finset.univ : Finset U).erase x
  let T : Finset V := G.image f
  have hx : x ∈ (Finset.univ : Finset U) := Finset.mem_univ x
  have hGCard : G.card = Fintype.card U - 1 := by
    simpa [G] using Finset.card_erase_of_mem hx
  have hTCard : T.card ≤ j := by
    have hImage : T.card ≤ G.card := Finset.card_image_le
    omega
  let R : Set V := (↑T : Set V) ∪ Set.range a
  have hRange (y : U) : f y ∈ R := by
    by_cases hy : y = x
    · right
      simpa [hy] using hAnchor
    · left
      exact Finset.mem_image.mpr
        ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, rfl⟩
  have hfR : IsClosedUHomomorphismEmbedding rules
      Source (Old.induce R)
      (fun y : U => ⟨f y, hRange y⟩) :=
    (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf).codRestrict
      R hRange
  have hCompleted : HasClosedUKCompletion K rules (Old.induce R) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hRooted T a hTCard)
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr
    (hCompleted.precomp_closedMap hfR)

/-- In the maximal intrinsic U-rank branch, an ORDINARY old-Picture
homomorphism-embedding becomes protected automatically. Thus even if
the Old map is INJECTIVE and no vertex collision occurs, a single
source vertex lying in some full Old A-copy gives an actual completion
from rooted W_j^A, WITHOUT any |A|<=j requirement.

The existence of that anchored vertex in the native Picture remains
a separate genuine Hales--Jewett history obligation. -/
theorem inducedClosed2019_maximal_ordinary_map_one_A_anchor
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U V P : Type v}
    [Fintype U]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : RelStructure L V)
    (A : RelStructure L P)
    (f : U → V)
    (hf : Source.IsHomomorphismEmbedding Old f)
    (j : ℕ) (hCard : Fintype.card U ≤ j+1)
    (a : Embedding A Old)
    (x : U) (hAnchor : f x ∈ Set.range a)
    (hRooted : Has2019RootedWeakSizeCompletions K rules Old A j) :
    HasInducedClosedUKCompletion K rules Source :=
  inducedClosed2019_weaksize_completion_of_one_A_anchor
    Source Old A f
    (IsClosedUHomomorphismEmbedding.toInducedClosed
      (hf.toClosedMap_of_max_USize hMax))
    j hCard a x hAnchor hRooted

end AllThoseRamseyClasses.Published
