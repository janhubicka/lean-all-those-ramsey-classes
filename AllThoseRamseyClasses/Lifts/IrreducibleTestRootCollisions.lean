import AllThoseRamseyClasses.Lifts.GeometricIrreducibleRootImage

/-!
# Root-image collisions and irreducible tests

An EHN homomorphism-embedding can identify distinct vertices, but cannot
identify two vertices simultaneously contained in the image of one FULL
embedding of an irreducible source test. This is stronger than demanding
that the entire induced closed separating root be irreducible.

We isolate a sufficient pairwise covering condition for injectivity on
a specified root and prove that a root-image collision witnesses failure
of this condition. The covering condition is NOT known to hold for the
minimal separators of Section 3 in general; no injective image quotient
or mixed-piece descent is postulated here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every pair of different vertices in R is contained in the image
of SOME full irreducible substructure of Source. The test may contain
vertices outside R; no irreducibility assumption is made on the induced
closed structure on R itself. -/
def RootPairsCoveredByIrreducibleTests
    {V : Type} (Source : Structure L V) (R : Set V) : Prop :=
  ∀ x y : V, x ∈ R → y ∈ R → x ≠ y →
    ∃ (W : Type) (E : Structure L W),
      E.Irreducible ∧
      ∃ (e : Structure.Embedding E Source) (a b : W),
        e a = x ∧ e b = y

/-- Pairwise coverage by genuine irreducible full source tests
implies injectivity of any EHN homomorphism-embedding ON R.
The map need not be injective away from R. -/
theorem ehn_injOn_of_rootPairsCoveredByIrreducibleTests
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (R : Set V)
    (hCovered : RootPairsCoveredByIrreducibleTests Source R) :
    Set.InjOn f R := by
  intro x hx y hy hxy
  by_contra hne
  obtain ⟨W, E, hIrr, e, a, b, ha, hb⟩ :=
    hCovered x y hx hy hne
  obtain ⟨g, hg⟩ := hf.2 E hIrr e
  have hga : g a = f x := (hg a).trans (congrArg f ha)
  have hgb : g b = f y := (hg b).trans (congrArg f hb)
  have hab : a = b :=
    g.injective (hga.trans (hxy.trans hgb.symm))
  exact hne (by
    calc
      x = e a := ha.symm
      _ = e b := congrArg e hab
      _ = y := hb)

/-- Injectivity of ordered geometric roots follows under pairwise
irreducible-test coverage, even when their complete induced
function-closed root structure is reducible. -/
theorem geometricRootImage_injective_of_pairwiseIrreducibleTestCover
    {V UT : Type}
    (Source : Structure L V)
    {n : ℕ}
    (d : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hCovered : RootPairsCoveredByIrreducibleTests
      Source (Set.range d.roots)) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  have hInjOn : Set.InjOn f (Set.range d.roots) :=
    ehn_injOn_of_rootPairsCoveredByIrreducibleTests
      Source Target f hf (Set.range d.roots) hCovered
  intro i j hij
  exact d.roots_injective
    (hInjOn ⟨i, rfl⟩ ⟨j, rfl⟩ hij)

/-- A genuine collision of ordered geometric-root images means the
root is NOT pairwise covered by any family of full irreducible
source tests. This sharpens the necessary condition 'root reducible':
the full tests are allowed to extend outside the root. -/
theorem geometricRoot_not_pairwiseIrreducibleTestCovered_of_collision
    {V UT : Type}
    (Source : Structure L V)
    {n : ℕ}
    (d : GeometricFunctionalPieceData Source n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (hCollision : ¬ Function.Injective
      (fun i : Fin n => f (d.roots i))) :
    ¬ RootPairsCoveredByIrreducibleTests
      Source (Set.range d.roots) := by
  intro hCovered
  exact hCollision
    (geometricRootImage_injective_of_pairwiseIrreducibleTestCover
      Source d Target f hf hCovered)

end AllThoseRamseyClasses.Lifts
