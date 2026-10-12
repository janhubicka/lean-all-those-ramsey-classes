import AllThoseRamseyClasses.Published.NativeZeroActiveCoreCompletion2019

/-!
# Corrected 2019 Lemma 2.30: ZERO active native history needs NO rank hypothesis

The earlier genuine native power-core completion PR #152 assumed that the
EXACT weak test had maximal intrinsic U-size, in order to upgrade its
ordinary core projection to a corrected protected map.

That rank assumption is unnecessary when the projection of the original
weak source to the temporary native attachment is ALREADY protected
under the corrected Definition 2.15 convention (as it is when restricting
a protected map from the closed full Picture).

This file proves the general underlying factorization:
if a corrected protected map f : Source -> Whole has its entire range
in the FULL embedded image e : B -> Whole, then f factors as a corrected
protected map Source -> B. No injectivity of f, closedness of Source
or Whole, or closure of the tested range is needed. Protection is checked
on each genuine embedded intrinsically closed irreducible test by
factoring its already-protected embedding through e.

Apply this to the true native attachment's embedded power core.
If an exact weak source meets NO private exterior copy indices,
its protected projection factors through the core. Composing the
factor with the existing protected power-part map into A∈K yields
a corrected K-completion of the ORIGINAL exact weak source.

CRUCIALLY this now handles zero-active tests of EVERY intrinsic U-rank,
not just maximum rank. It neither uses R_j nor W_j. The remaining
nonmaximal-rank tests whose projections meet exterior copies, and the
transverse common A-root/history geometry, are genuinely unresolved.
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

/-- Any corrected protected map into the full embedded image of B
factors as a corrected protected map into B itself. Source and
target may be weak and nonclosed, and f need not be injective.

This is stronger than the earlier ORDINARY HE range factorization:
its protected-test proof requires no maximal intrinsic U-rank. -/
theorem inducedClosed2019_factor_protected_through_embedded_range
    {rules : ClosureDescription L}
    {U V W : Type v}
    (Source : RelStructure L U)
    (B : RelStructure L V)
    (Whole : RelStructure L W)
    (f : U → W)
    (hf : IsInducedClosedUHomomorphismEmbedding rules Source Whole f)
    (e : Embedding B Whole)
    (hRange : ∀ x : U, ∃ b : V, f x = e b) :
    ∃ g : U → V,
      IsInducedClosedUHomomorphismEmbedding rules Source B g ∧
      ∀ x : U, f x = e (g x) := by
  classical
  let g : U → V := fun x => Classical.choose (hRange x)
  have hg (x : U) : f x = e (g x) :=
    Classical.choose_spec (hRange x)
  have hHom : Source.IsHomomorphism B g := by
    intro R xs hxs
    have hTarget : Whole.rel R (e ∘ (g ∘ xs)) := by
      convert hf.1 R xs hxs using 1
      funext i
      exact (hg (xs i)).symm
    exact (e.map_rel_iff R (g ∘ xs)).mp hTarget
  have hAbstract :
      IsClosedUHomomorphismEmbedding rules Source Whole f :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf
  have hFactored :
      IsClosedUHomomorphismEmbedding rules Source B g := by
    refine ⟨hHom, ?_⟩
    intro X Test hClosed hIrred d
    obtain ⟨k, hk⟩ := hAbstract.on_test Test hClosed hIrred d
    have hKRange (x : X) : ∃ b : V, k x = e b := by
      refine ⟨g (d x), ?_⟩
      calc
        k x = f (d x) := hk x
        _ = e (g (d x)) := hg (d x)
    let kB : Embedding Test B :=
      k.factorThroughRange e hKRange
    refine ⟨kB, ?_⟩
    intro x
    apply e.injective
    calc
      e (kB x) = k x :=
        (Classical.choose_spec (hKRange x)).symm
      _ = f (d x) := hk x
      _ = e (g (d x)) := hg (d x)
  exact ⟨g,
    IsClosedUHomomorphismEmbedding.toInducedClosed hFactored,
    hg⟩

/-- The genuine native zero-private-copy branch for ANY protected weak
source, with NO intrinsic rank hypothesis and NO old completion
invariant. The source is completed directly in selected A∈K through
the actual power core; temporary native attachment need not be closed. -/
theorem native2019_protected_zero_active_has_A_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V I U : Type v} {N : ℕ}
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
    (hNoPrivate : ∀ x : U, ∀ i : I,
      ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)) :
    HasInducedClosedUKCompletion K rules Source := by
  let Core := (power (Old.restrict alpha) N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let eCore : Embedding Core
      (attach Old.toRelStructure (Old.support alpha) Core maps) :=
    coreEmbedding Old.toRelStructure (Old.support alpha) Core maps
  have hRange (x : U) :
      ∃ w : NonInduced.Vertex (Old.restrict alpha) N,
        p x = eCore w := by
    cases hx : p x with
    | inl w =>
        exact ⟨w, rfl⟩
    | inr pair =>
        have hout : OutsideAt
            (W := NonInduced.Vertex (Old.restrict alpha) N)
            (I := I) (Old.support alpha) pair.1 (p x) :=
          ⟨pair.2, hx⟩
        exact False.elim ((hNoPrivate x pair.1) hout)
  obtain ⟨q, hq, _⟩ :=
    inducedClosed2019_factor_protected_through_embedded_range
      Source Core
      (attach Old.toRelStructure (Old.support alpha) Core maps)
      p hp eCore hRange
  have hToA : IsClosedUHomomorphismEmbedding rules Source A
      ((power (Old.restrict alpha) N).part ∘ q) :=
    hPower.comp
      (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hq)
  exact ⟨Q, inferInstance, A, hAK, hAIrred,
    (power (Old.restrict alpha) N).part ∘ q,
    IsClosedUHomomorphismEmbedding.toInducedClosed hToA⟩

end AllThoseRamseyClasses.Published
