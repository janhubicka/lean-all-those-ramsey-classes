import AllThoseRamseyClasses.Published.NativeExactActiveSubhistory2019
import AllThoseRamseyClasses.Published.NativeRestSourceOrdinary2019
import AllThoseRamseyClasses.Published.InducedClosed2019RankCollision
import PartiteConstruction.Ramsey.ClosureMaximalWeakImageTransfer

/-!
# Corrected 2019 exact weak-size proof: actual ACTIVE common-coordinate maps

A full native Hales--Jewett Picture generally has no common parameter
coordinate. But a particular EXACT weak tested source uses only the
copy indices actually visited by PRIVATE exterior vertices.

This file constructs an ORDINARY homomorphism-embedding from the
original exact weak source into Old if all of its ACTUAL private-active
HJ lines share one variable coordinate. It works by a genuine induced
factorization through precisely that source-active subattachment and
the checked coordinate/identity fold; no global injectivity, source
closedness, or temporary target semiclosedness is assumed.

Second, we prove a true weak-j induction collision branch:
a finite source of MAXIMAL intrinsic U-size and <=j+1 vertices
admits a corrected K-completion from ONLY the previous exact W_j(Old)
invariant if an actual ordinary Old-side map identifies two distinct
source vertices. The projected WEAK image then has at most j vertices
and is completed directly. We do NOT invoke any completion of its
potentially much larger closed hull, avoiding ATRC-020.

The strict j+1 noncolliding case, nonmaximal-rank weak source case,
transverse active-line REST coherence, and common A-boundary remain
OPEN. No general repaired Theorem 2.18 is asserted.
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

/-- Actual exact weak source factorization through its source-active
native subattachment, followed by the selected coordinate/identity
ordinary old-Picture fold. Activity is defined by ORIGINAL source
private exteriors, and all unvisited copy indices are irrelevant. -/
theorem native2019_actual_active_common_coordinate_old_ordinary
    {P Q V U I : Type v} {N : ℕ}
    (Source : RelStructure L U)
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
    (k : Fin N)
    (hCommon : ∀ i : I,
      (∃ x : U, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)) →
      (lines i).symbol k = .parameter) :
    ∃ q : U → V,
      Source.IsHomomorphismEmbedding Old.toRelStructure q := by
  classical
  let Support := Old.support alpha
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let J : Set I := {i | ∃ x : U,
    OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) Support i (p x)}
  obtain ⟨g, hg, _⟩ :=
    native2019_exact_source_factors_all_active_subhistory
      Source Old.toRelStructure Support Core maps p hp
  let r : Vertex Support
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := J) → V :=
    fold
      (fun z : NonInduced.Vertex (Old.restrict alpha) N =>
        (z.coord k).1)
      (fun (_ : J) (x : V) => x)
  have hr :
      (attach Old.toRelStructure Support Core
        (fun i : J => maps i.1)).IsHomomorphismEmbedding
        Old.toRelStructure r :=
    native2019_selected_set_coordinate_isOrdinaryHE
      Old alpha A hRestricted lines J k
        (fun i hi => hCommon i hi)
  exact ⟨r ∘ g, hr.comp hg⟩

/-- An ORDINARY old-picture map of a maximal-rank exact weak source
with a REAL vertex collision has weak projected image cardinal <=j.
Consequently W_j(Old), rather than R_j(Old), suffices for a corrected
K-completion of the original j+1-vertex source.

The ordinary map itself can be constructed by the active common
coordinate theorem above; a collision on that map must still be
verified for the particular tested source. -/
theorem inducedClosed2019_maximal_weak_ordinary_collision_of_Wj
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U V : Type v}
    [Fintype U] [Finite V]
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (hMax : USize rules Source = Fintype.card U)
    (q : U → V)
    (hq : Source.IsHomomorphismEmbedding Old q)
    (j : ℕ) (hTotal : Fintype.card U ≤ j+1)
    (x y : U) (hxy : x ≠ y) (hCollision : q x = q y)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.induce (↑T : Set V))) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let T : Finset V := Finset.univ.image q
  have hStrict :
      T.card < (Finset.univ : Finset U).card :=
    projected_generator_card_lt (Finset.univ : Finset U)
      q (Finset.mem_univ x) (Finset.mem_univ y) hxy hCollision
  have hCard : T.card ≤ j := by
    simp only [Finset.card_univ] at hStrict
    omega
  have hRange (z : U) : q z ∈ (↑T : Set V) :=
    Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hProtected : IsClosedUHomomorphismEmbedding rules
      Source Old q :=
    hq.toClosedMap_of_max_USize hMax
  have hImage : HasClosedUKCompletion K rules
      (Old.induce (↑T : Set V)) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hOldWeak T hCard)
  have hSource : HasClosedUKCompletion K rules Source :=
    hImage.precomp_closedMap
      (hProtected.codRestrict (↑T : Set V) hRange)
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hSource

end AllThoseRamseyClasses.Published
