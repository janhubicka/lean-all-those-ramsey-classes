import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureRankOneBase
import PartiteConstruction.Ramsey.ClosureWeakHullUSize

/-!
# Exact WEAK intrinsic U-rank-one sources are already B-covered

A simplification of corrected 2019 Lemma 2.30:
the original closed-irreducible B-copy coverage of a U-CLOSED Picture
completes EVERY EXACT WEAK induced substructure of intrinsic U-size
at most ONE, not merely the U-closed rank-one tests.

The tested weak source F=C|S may be arbitrarily large, and is NOT
assumed U-closed. Its own minimum generating set has at most one
vertex. The upstream weak ambient-hull rank theorem proves that
the ambient CLOSED hull H=cl_U^C(S) has USize(H)<=USize(F)<=1.
Since C is U-closed, H is intrinsically U-closed. The genuine
rank-one irreducibility theorem now says H is intrinsically
U-irreducible; the original B-coverage gives a FULL embedding
H->B. Restrict it to the ORIGINAL weak vertex carrier S to obtain
a full embedding F->B and an actual corrected (K,U)-completion.

There is no appeal to a completion of a generating weak subset,
no illicit extension of its map to a prescribed hull, and no
assumption that the source weak F itself is closed or small.
The B-embedding is first provided on the ACTUAL closed hull by
the original closed irreducible COVERAGE, and only then restricted.

This is a genuine new NONMAXIMAL intrinsic-rank completion branch
requiring no native Hales--Jewett source history, protected map
to old Picture, or previous W_j/R_j/rooted W_j^K invariant.
It does NOT complete weak tests of intrinsic U-rank >=2, prove
the native higher-rank j->j+1 successor, or establish Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Every finite EXACT WEAK induced source of intrinsic U-size <=1 in
a U-CLOSED old Picture has a corrected completion into the SAME
original fixed irreducible B∈K, whenever the Picture satisfies
the original closed U-irreducible B-copy coverage.

The weak source is not closed; its AMBIENT hull is covered by B.
There is no cardinal bound on the tested source itself or its hull. -/
theorem inducedClosed2019_exact_weak_USize_le_one_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VB : Type v}
    [Finite VC] [Finite VB]
    (C : RelStructure L VC)
    (B : RelStructure L VB)
    (hC : IsUClosed rules C)
    (hBK : K B)
    (hBIrred : B.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test C →
      Nonempty (Embedding Test B))
    (S : Finset VC)
    (hRank : USize rules (C.induce (↑S : Set VC)) ≤ 1) :
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set VC)) := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  let H : Set VC := UClosureHull rules C (↑S : Set VC)
  letI : Fintype H := Fintype.ofFinite H
  have hHClosed : IsUClosed rules (C.induce H) :=
    hC.induce_UClosureHull (↑S : Set VC)
  have hHRank : USize rules (C.induce H) ≤ 1 :=
    (USize_induce_ambient_hull_le_weak
      rules C (↑S : Set VC)).trans hRank
  have hHIrred : IsUIrreducible rules (C.induce H) :=
    hHClosed.uIrreducible_of_USize_le_one hHRank
  obtain ⟨e⟩ := hCover (C.induce H) hHClosed hHIrred
    (inclusion C H)
  let includeWeak : Embedding
      (C.induce (↑S : Set VC)) (C.induce H) := {
    toFun := fun x =>
      ⟨x.1, subset_UClosureHull rules C (↑S : Set VC) x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : H => z.1) hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let g : Embedding (C.induce (↑S : Set VC)) B :=
    e.comp includeWeak
  have hCompleted : HasClosedUKCompletion K rules
      (C.induce (↑S : Set VC)) :=
    ⟨VB, inferInstance, B, hBK, hBIrred,
      g, g.isClosedUHomomorphismEmbedding rules⟩
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hCompleted

end AllThoseRamseyClasses.Published
