import AllThoseRamseyClasses.Published.NativeTwoRestFree2019
import AllThoseRamseyClasses.Published.NativeTwoActiveRestOrdinary2019
import AllThoseRamseyClasses.Published.NativeTwoRestRootCompletion2019

/-!
# Actual two-active native HJ source: FREE RESTS, TWO Old maps, completable root

For two source-private-active native copies i,j, the two complementary
REST source sets (excluding private exterior j, respectively i) form
an actual relational free cover, EVEN when power-core relation tuples
cross the exclusive HJ line images. The exact REST pieces have TWO
ordinary old-Picture homomorphism-embeddings, each using its own genuine
HJ parameter coordinate. The literal common REST root lies entirely
in the core and has a corrected K-completion in selected A.

This unifies the verified native facts into one original-source
interface. When both private exteriors occur the split is proper,
without global map injectivity or closure of tested weak source.

THE MISSING STEP REMAINS: an arbitrary protected (possibly noninjective)
K-completion of the core root is NOT a single common CLOSED K-boundary
that embeds fully into BOTH old-side projected completions.
No higher-rank successor or main theorem is claimed.
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

/-- Package the four genuine facts for EXACT complementary native
REST pieces under an original corrected PROTECTED projection and
its separate ORDINARY reflection on a closed full source:

1. literal source free cover,
2. two genuine OLD homomorphism-embeddings on its exact sides,
3. the literal core intersection admits a corrected K-completion,
4. both private-active witnesses make the source cut proper.

No full common K-boundary embeddings are asserted. -/
theorem native2019_two_active_rest_unified_geometry
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Finite Q]
    (Source : RelStructure L U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (hpOrd : Source.IsHomomorphismEmbedding
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
      (I := I) (Old.support alpha) j (p y)) :
    let Left : Set U := {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x)}
    let Right : Set U := {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
    IsFreeAmalgam
      (exactFreeCoverRootToLeft Source Left Right)
      (exactFreeCoverRootToRight Source Left Right)
      (inclusion Source Left) (inclusion Source Right) ∧
    (∃ (fL : Left → V) (fR : Right → V),
      (Source.induce Left).IsHomomorphismEmbedding
        Old.toRelStructure fL ∧
      (Source.induce Right).IsHomomorphismEmbedding
        Old.toRelStructure fR) ∧
    HasInducedClosedUKCompletion K rules
      (Source.induce (Left ∩ Right)) ∧
    Nonempty (ProperFreeDecomposition Source) := by
  classical
  let Left : Set U := {x | ¬ OutsideAt
    (W := NonInduced.Vertex (Old.restrict alpha) N)
    (I := I) (Old.support alpha) j (p x)}
  let Right : Set U := {x | ¬ OutsideAt
    (W := NonInduced.Vertex (Old.restrict alpha) N)
    (I := I) (Old.support alpha) i (p x)}
  have hFree :
      IsFreeAmalgam
        (exactFreeCoverRootToLeft Source Left Right)
        (exactFreeCoverRootToRight Source Left Right)
        (inclusion Source Left) (inclusion Source Right) :=
    native2019_positive_two_rest_source_free
      Source Old.toRelStructure (Old.support alpha)
      (power (Old.restrict alpha) N).toRelStructure
      (closureLineMaps Old alpha A hRestricted lines)
      p hp.1 i j hij
  obtain ⟨fL, fR, hfL, hfR⟩ :=
    native2019_two_only_active_rest_ordinary_old_maps
      Source Old alpha A hRestricted lines p hpOrd i j hij hOnly
  have hRoot :
      HasInducedClosedUKCompletion K rules
        (Source.induce (Left ∩ Right)) := by
    have h :=
      native2019_two_only_active_rest_root_has_A_completion
        Source Old alpha A hAK hAIrred hRestricted hPower
        lines p hp i j hij hOnly
    simpa only [Left, Right, Set.inter_def, Set.mem_setOf_eq] using h
  have hProper : Nonempty (ProperFreeDecomposition Source) :=
    native2019_two_private_active_rest_cut_proper
      Source Old.toRelStructure (Old.support alpha)
      (power (Old.restrict alpha) N).toRelStructure
      (closureLineMaps Old alpha A hRestricted lines)
      p hp.1 i j hij hActiveI hActiveJ
  exact ⟨hFree, ⟨fL, fR, hfL, hfR⟩, hRoot, hProper⟩

end AllThoseRamseyClasses.Published
