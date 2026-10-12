import AllThoseRamseyClasses.Published.NativeOldCopyWeakPiece2019
import AllThoseRamseyClasses.Published.NativeCoreRootBoundary2019
import AllThoseRamseyClasses.Published.NativeFiniteActiveHistory2019

/-!
# Native 2019 strict-rank history: ZERO active exterior copies complete via A

A possibly weak exact tested source projecting into an actual native
Hales--Jewett attachment may meet NO private exterior copy vertices.
Then the entire original source map factors through the genuine
embedded power core; no Hales--Jewett line index is needed.

At maximum intrinsic U-size, an ORDINARY source homomorphism-embedding
into that core protects closed U-irreducible tests automatically.
Composing with the actual protected part map from the power core to
the selected closed A in K gives a corrected completion of the WHOLE
original exact weak source into A. Its vertex carrier is unchanged.

This discharges a genuine zero-active-line branch of the weak-size
j->j+1 history without the old closed-rank-j completion hypothesis,
weak-image hull or false common-coordinate assumption.
The full source may be nonclosed and its projection noninjective.

The branch with one active line, transverse active lines,
nonmaximal weak rank, and common A-boundary coherence remain separate.
No unconditional repaired Theorem 2.18 is claimed.
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
variable {P Q V I U : Type v} {N : ℕ}

/-- If an exact weak maximal-U-rank source maps ordinarily to the
ACTUAL attachment with range entirely in its embedded power core,
the prescribed core part map gives a corrected K-completion in A.
Neither the source nor the native attachment must be U-closed. -/
theorem native2019_maximal_weak_core_range_has_A_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    [Fintype U] [Finite Q]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (hCoreRange : ∀ x : U,
      ∃ w : NonInduced.Vertex (Old.restrict alpha) N,
        p x = Sum.inl w) :
    HasInducedClosedUKCompletion K rules Source := by
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let eCore : Embedding Core
      (attach Old.toRelStructure (Old.support alpha) Core maps) :=
    coreEmbedding Old.toRelStructure (Old.support alpha) Core maps
  have hRange (x : U) : ∃ w : NonInduced.Vertex
      (Old.restrict alpha) N, p x = eCore w := by
    obtain ⟨w, hw⟩ := hCoreRange x
    exact ⟨w, hw⟩
  obtain ⟨q, hq, _⟩ :=
    ordinaryHE_factor_through_embedded_copy_2019 hp eCore hRange
  have hProtected :
      IsClosedUHomomorphismEmbedding rules Source Core q :=
    hq.toClosedMap_of_max_USize hMax
  have hToA : IsClosedUHomomorphismEmbedding rules Source A
      ((power (Old.restrict alpha) N).part ∘ q) :=
    hPower.comp hProtected
  exact ⟨Q, inferInstance, A, hAK, hAIrred,
    (power (Old.restrict alpha) N).part ∘ q,
    IsClosedUHomomorphismEmbedding.toInducedClosed hToA⟩

/-- Concrete ZERO private-exterior history: the absence of an active
copy index forces the original source image into the genuine power
core, and therefore completes it in A by the preceding theorem.
The exact source's intrinsic maximum U-rank is still required. -/
theorem native2019_maximal_weak_zero_active_has_A_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    [Fintype U] [Finite Q]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (hNoPrivate : ∀ x : U, ∀ i : I,
      ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)) :
    HasInducedClosedUKCompletion K rules Source := by
  have hCoreRange (x : U) :
      ∃ w : NonInduced.Vertex (Old.restrict alpha) N,
        p x = Sum.inl w := by
    cases hx : p x with
    | inl w =>
        exact ⟨w, hx⟩
    | inr pair =>
        have hout : OutsideAt
            (W := NonInduced.Vertex (Old.restrict alpha) N)
            (I := I) (Old.support alpha) pair.1 (p x) :=
          ⟨pair.2, hx⟩
        exact False.elim ((hNoPrivate x pair.1) hout)
  exact native2019_maximal_weak_core_range_has_A_completion
    Source hMax Old alpha A hAK hAIrred
    hPower hRestricted lines p hp hCoreRange

end AllThoseRamseyClasses.Published
