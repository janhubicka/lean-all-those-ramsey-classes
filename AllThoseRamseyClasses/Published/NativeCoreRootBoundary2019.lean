import AllThoseRamseyClasses.Published.NativePowerCoordinateParts2019
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization
import PartiteConstruction.Ramsey.ClosurePictureCoordinate

/-!
# A fixed A-boundary map for actual native Hales--Jewett core roots

The higher-rank repaired 2019 Lemma 2.30 must glue completions of
different source sides through ONE common closed K-boundary.
Coordinate evaluations into the old Picture generally disagree
as vertices, even when they have identical part labels.

In the TRUE native power core R^N, its part projection to the
selected closed structure A is already a protected closed-test
map when the power is protected. For any exact source root T
embedded into that core, restricting the part projection gives
an explicit corrected homomorphism-embedding q:T->A.
The images of ALL coordinate evaluations of the root in Old
have the SAME outer parts, namely alpha(q(x)).

If A is finite, in K and ordinary irreducible, q is itself a
fully valid amended (K,U)-completion of the exact root T
into the fixed target A, without closing the tested root or
assuming that q is globally injective.

This constructs the NATURAL COMMON A-TARGET and the protected
root map needed for a future mixed-cut completion argument.
It does NOT automatically embed all of A into two separate
old-picture projected side completions. That coherence and the
proper source free cut remain open. No general strict rank
increment or unconditional repaired Theorem 2.18 is asserted.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced

universe u v
variable {L : RelLanguage.{u}}
variable {P Q V X : Type v} {N : ℕ}

/-- The restriction of the genuine native power's part projection
to an arbitrary fully embedded root T is a corrected protected
map q:T->A. Every coordinate evaluation followed by Old.part
equals alpha∘q on the ORIGINAL root vertices. -/
theorem nativeCoreRoot_protected_A_boundary_and_part_compatibility
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P)
    (A : RelStructure L Q)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (Root : RelStructure L X)
    (e : RelStructure.Embedding Root
      (power (Old.restrict alpha) N).toRelStructure) :
    IsInducedClosedUHomomorphismEmbedding rules Root A
      ((power (Old.restrict alpha) N).part ∘ e) ∧
    (∀ k : Fin N, ∀ x : X,
      Old.part ((e x).coord k).1 =
        alpha (((power (Old.restrict alpha) N).part) (e x))) := by
  have hRoot :
      IsClosedUHomomorphismEmbedding rules Root A
        ((power (Old.restrict alpha) N).part ∘ e) :=
    hPower.precomp_embedding e
  refine ⟨IsClosedUHomomorphismEmbedding.toInducedClosed hRoot, ?_⟩
  intro k x
  change Old.part ((e x).coord k).1 = alpha (e x).part
  exact nativePower_selected_coordinate_old_part Old alpha N (e x) k

/-- A finite irreducible A in K completes ANY exact embedded source
root of the native power core, by the ACTUAL protected part map.
The K-target A is explicit; no part labels are assigned to an
arbitrary unrelated completion target. -/
theorem nativeCoreRoot_has_actual_A_K_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (Old : System L P V) (alpha : Q ↪ P)
    (A : RelStructure L Q) [Finite Q]
    (hKA : K A) (hAIrred : A.Irreducible)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (Root : RelStructure L X)
    (e : RelStructure.Embedding Root
      (power (Old.restrict alpha) N).toRelStructure) :
    HasInducedClosedUKCompletion K rules Root := by
  obtain ⟨hq, _⟩ :=
    nativeCoreRoot_protected_A_boundary_and_part_compatibility
      Old alpha A hPower Root e
  exact ⟨Q, inferInstance, A, hKA, hAIrred,
    (power (Old.restrict alpha) N).part ∘ e, hq⟩

end AllThoseRamseyClasses.Published
