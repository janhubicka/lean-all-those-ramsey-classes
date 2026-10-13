import AllThoseRamseyClasses.Published.NativeTwoRestFree2019
import AllThoseRamseyClasses.Published.NativeTwoActiveRestOrdinary2019
import AllThoseRamseyClasses.Published.ClosedKRootTwoSide2019

/-!
# Complete genuine two-REST native tests when the literal root is closed and in K

This is a mathematically sharp conditional instance of corrected 2019
Lemma 2.30, following the detailed English proof in
docs/lemma230-two-rest-closed-K-root-case-20261013.md (PR #181).

For an exact maximal-U-size weak source F with <=rank+1 ORIGINAL
vertices, let p:F->Attach(Old,Power,lines) be an ordinary (possibly
noninjective) native homomorphism-embedding, and suppose the only
source-private-active copy indices are two distinct i,j.

The ACTUAL complementary REST pieces

  Left = {x | p(x) is not in private exterior j},
  Right = {x | p(x) is not in private exterior i}

form a genuine RELATIONAL free source cover, regardless of
crossing power-core relations. Each has an ordinary map to Old
using its own genuine HJ line parameter coordinate (PR #177).
Their intersection is precisely the tested source whose vertices
project entirely into the actual power CORE (PR #178).

Here we impose explicitly the remaining strong sufficient
hypothesis: this literal induced source intersection is ITSELF
a U-CLOSED member of the irreducible K-class. Then ordinary
old maps restrict to FULL embeddings of this SAME K-root into Old.
The rank-j two-side gluing lemma (CI-green PR #180) completes F
using the previous CLOSED rank-j invariant.

This does NOT derive intrinsic closure/K-membership of an arbitrary
native core root from its possibly noninjective K-completion
(PR #178). PR #179 gives a sharp counterexample to replacing full
root embeddings by one fixed A-letter. Nothing here establishes
the general native successor or repaired Theorem 2.18.
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

/-- Complete an ORIGINAL exact maximal-U-rank weak source from the
TRUE two-REST source free split when the WHOLE literal core root is
already a U-closed K-member. Source map need only be ordinary,
possibly noninjective; the temporary native target need not be
U-closed or U-semiclosed.

The old completion premise is closed R_rank, not the weaker W_rank.
There is no invented word-A embedding on the root. -/
theorem native2019_two_active_rest_closed_K_root_completion
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
      ({x : U |
        ¬ OutsideAt (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x) ∧
        ¬ OutsideAt (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)} : Set U)))
    (hRootClosed : IsUClosed rules (Source.induce
      ({x : U |
        ¬ OutsideAt (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x) ∧
        ¬ OutsideAt (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)} : Set U)))
    (rank : ℕ) (hTotal : Fintype.card U ≤ rank + 1)
    (hOldClosed : IsUClosed rules Old.toRelStructure)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X),
      K T → T.Irreducible)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ rank →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let Left : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x)}
  let Right : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source Left Right)
        (exactFreeCoverRootToRight Source Left Right)
        (inclusion Source Left) (inclusion Source Right) :=
    native2019_positive_two_rest_source_free
      Source Old.toRelStructure (Old.support alpha) Core
      maps p hp.1 i j hij
  obtain ⟨fL, fR, hfL, hfR⟩ :=
    native2019_two_only_active_rest_ordinary_old_maps
      Source Old alpha A hRestricted lines
      p hp i j hij hOnly
  let d : ProperFreeDecomposition Source := {
    Common := {x : U // x ∈ Left ∩ Right}
    Left := Left
    Right := Right
    common := Source.induce (Left ∩ Right)
    left := Source.induce Left
    right := Source.induce Right
    toLeft := exactFreeCoverRootToLeft Source Left Right
    toRight := exactFreeCoverRootToRight Source Left Right
    leftIn := inclusion Source Left
    rightIn := inclusion Source Right
    free := hFree
    leftProper := by
      intro hSurj
      obtain ⟨x, hx⟩ := hActiveJ
      obtain ⟨y, hy⟩ := hSurj x
      change y.1 = x at hy
      exact (hy ▸ y.2) hx
    rightProper := by
      intro hSurj
      obtain ⟨x, hx⟩ := hActiveI
      obtain ⟨y, hy⟩ := hSurj x
      change y.1 = x at hy
      exact (hy ▸ y.2) hx
  }
  letI : Finite d.Common :=
    Finite.of_injective (fun x : d.Common => x.1) Subtype.val_injective
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  have hLCard : Fintype.card d.Left < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.leftIn d.leftIn.injective d.leftProper
  have hRCard : Fintype.card d.Right < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective
      d.rightIn d.rightIn.injective d.rightProper
  have hSmallL : Fintype.card d.Left ≤ rank := by omega
  have hSmallR : Fintype.card d.Right ≤ rank := by omega
  have hK : K d.common := hRootK
  have hClosed : IsUClosed rules d.common := hRootClosed
  exact inducedClosed2019_maximal_weak_two_old_maps_glue_of_closed_K_root
    d.free hMax Old.toRelStructure hOldClosed
    hStrong hHer hKIrr hK hClosed
    fL fR hfL hfR
    rank hSmallL hSmallR hOldRank

end AllThoseRamseyClasses.Published
