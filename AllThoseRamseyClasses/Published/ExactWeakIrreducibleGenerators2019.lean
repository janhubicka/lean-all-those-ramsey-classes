import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import PartiteConstruction.Ramsey.ClosureWeakHullUSize

/-!
# Exact weak tests with an IRREDUCIBLE U-generating seed are already covered by B

The original 2019 Picture's U-closed and closed-U-irreducible
B-copy coverage hypotheses imply corrected K-completions of ANY
exact weak induced test F which has an ORDINARY IRREDUCIBLE
U-generating weak seed G, irrespective of F's intrinsic U-rank
or vertex cardinality.

The seed G is a subset of the ORIGINAL weak source vertices.
Because G generates F intrinsically, the ambient U-closure
cl_U^C(G) agrees with cl_U^C(F), by the verified
UClosureHull_of_induce_generators_eq lemma.
Because the seed is ORDINARY irreducible and C is U-closed,
its actual ambient closure is U-closed and U-irreducible.
The existing original B-copy coverage FULLY embeds that
entire closed ambient hull into the SAME B∈K.
Restrict to the ORIGINAL exact source F and obtain a
corrected K-completion without extension of any weak-source
completion map to the ambient hull.

This generalizes the existing weak ORDINARY irreducible test
completion (the entire weak test is its irreducible seed),
and explains the new intrinsic USize<=1 corollary: its
minimum generating seed is empty or singleton and hence
ordinary irreducible.

WARNING: not every U-generated weak test has an ordinary
irreducible generating seed. The upstream finite-seed
obstruction demonstrates that this cannot be assumed in
the unrestricted main theorem. This is a VERIFIED BRANCH,
not a complete rank-j+1 Picture constructor.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Original B-coverage completes every exact WEAK induced source
possessing an ordinary irreducible intrinsic U-generating seed,
even when the whole weak source is reducible and unclosed.

The test is completed by embedding its AMBIENT closed hull,
not by extending a weak generating-subset completion.
No rank or vertex bound is imposed on the source or seed. -/
theorem inducedClosed2019_exact_weak_of_irreducible_generating_seed
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VB : Type v}
    [Finite VC] [Finite VB]
    (C : RelStructure L VC)
    (B : RelStructure L VB)
    (hC : IsUClosed rules C)
    (hBK : K B) (hBIrred : B.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test C →
      Nonempty (Embedding Test B))
    (S : Set VC)
    (G : Set S)
    (hGen : IsUGenerating rules (C.induce S) G)
    (hSeed : (C.induce (Subtype.val '' G)).Irreducible) :
    HasInducedClosedUKCompletion K rules (C.induce S) := by
  classical
  let H : Set VC := UClosureHull rules C S
  have hHullEq :
      UClosureHull rules C (Subtype.val '' G) = H :=
    UClosureHull_of_induce_generators_eq rules C S G hGen
  have hHClosed : IsUClosed rules (C.induce H) :=
    hC.induce_UClosureHull S
  have hHIrred : IsUIrreducible rules (C.induce H) := by
    rw [← hHullEq]
    exact hC.irreducibleSeed_hull_isUIrreducible
      (Subtype.val '' G) hSeed
  obtain ⟨e⟩ := hCover (C.induce H) hHClosed hHIrred
    (inclusion C H)
  let embedWeak : Embedding (C.induce S) (C.induce H) := {
    toFun := fun x =>
      ⟨x.1, subset_UClosureHull rules C S x.2⟩
    injective := by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : H => z.1) hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let full : Embedding (C.induce S) B := e.comp embedWeak
  have hComplete : HasClosedUKCompletion K rules
      (C.induce S) :=
    ⟨VB, inferInstance, B, hBK, hBIrred,
      full, full.isClosedUHomomorphismEmbedding rules⟩
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hComplete

end AllThoseRamseyClasses.Published
