import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Functional.WeakOperations
import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces

/-!
# Factor EHN weak homomorphism-embeddings through a FULL target side

The 2019 lift flip starts with a weak homomorphism-embedding
f : Forbidden -> D into a full functional free amalgam D of two
ambient witnesses. If a selected forbidden piece has its entire
vertex image in the left side, its restriction must factor as a
weak EHN map into that side.

The upstream library already has the necessary two ingredients:
`Embedding.cancel_weak` cancels full target embeddings for global
positive relations and function incidences, while
`Embedding.factorWithMap` cancels a full embedding between any
closed irreducible test and the target.

Combining them gives a genuine EHN factorization, without the
invalid assertion that a globally weak map is a full embedding
or injective on an arbitrary root.

The geometric specialization supplies precisely the weak piece-side
map required by the verified common canonical-lift flip, whenever
the original forbidden source's piece images lie in that ambient
side. This does NOT supply root injectivity: it remains a separate
obligation in the main strong-amalgamation argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Cancel a FULL target embedding from an EHN homomorphism-embedding.

The ambient map p need only be weak globally. For each irreducible
source substructure, its witness full embedding in C factors into B
because the vertex map factors through j on the entire source. -/
theorem ehnHomomorphismEmbedding_cancel_full
    {U V W : Type v}
    {A : Structure L U} {B : Structure L V}
    {C : Structure L W}
    {p : U → W} {q : U → V}
    (hp : A.IsEHNHomomorphismEmbedding C p)
    (j : Structure.Embedding B C)
    (hfactor : ∀ x : U, p x = j (q x)) :
    A.IsEHNHomomorphismEmbedding B q := by
  have hpComp : A.IsWeakHomomorphism C (j ∘ q) := by
    have hfun : p = j ∘ q := by
      funext x
      exact hfactor x
    rw [← hfun]
    exact hp.1
  refine ⟨j.cancel_weak hpComp, ?_⟩
  intro X E hE e
  obtain ⟨gC, hgC⟩ := hp.2 E hE e
  let gB : Structure.Embedding E B :=
    gC.factorWithMap j (q ∘ e)
      (fun x => (hgC x).trans (hfactor (e x)))
  exact ⟨gB, fun _ => rfl⟩

/-- When the entire image of a weak EHN map p is contained in a
FULLY embedded target side B, construct an actual weak EHN map into
that side and prove that composing with its full inclusion recovers p.

This is a constructive factorization in Prop, not a new axiom
asserting the existence of a side map. -/
theorem ehnHomomorphismEmbedding_factor_full_side
    {U V W : Type v}
    {A : Structure L U} {B : Structure L V}
    {C : Structure L W}
    {p : U → W}
    (hp : A.IsEHNHomomorphismEmbedding C p)
    (j : Structure.Embedding B C)
    (hImage : ∀ x : U, ∃ y : V, p x = j y) :
    ∃ q : U → V,
      A.IsEHNHomomorphismEmbedding B q ∧
      ∀ x : U, j (q x) = p x := by
  classical
  let q : U → V := fun x => Classical.choose (hImage x)
  have hfactor : ∀ x : U, p x = j (q x) := by
    intro x
    exact Classical.choose_spec (hImage x)
  exact ⟨q, ehnHomomorphismEmbedding_cancel_full hp j hfactor,
    fun x => (hfactor x).symm⟩

/-- Geometric Section 3 application: the restriction of the original
weak forbidden-source map to an ACTUAL induced minimal-cut piece
factors into the chosen ambient side whenever all piece vertices
map into that side.

The produced map satisfies the whole irreducible-test EHN condition;
the root tuple is not silently asserted to be injectively mapped. -/
theorem geometricPieceWeakMap_factor_ambient_side
    {V UA UT : Type v}
    (Forbidden : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData Forbidden n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA)
    (jLeft : Structure.Embedding Left Target)
    (hContained : ∀ z : (geometricPieceVertices Forbidden d),
      ∃ a : UA, f z.1 = jLeft a) :
    ∃ pLeft : (geometricPieceVertices Forbidden d) → UA,
      (geometricFunctionalPiece Forbidden d).IsEHNHomomorphismEmbedding
        Left pLeft ∧
      ∀ z, jLeft (pLeft z) = f z.1 := by
  have hPiece :
      (geometricFunctionalPiece Forbidden d).IsEHNHomomorphismEmbedding
        Target (fun z => f z.1) :=
    hf.comp
      (geometricFunctionalPieceEmbedding Forbidden d).isEHNHomomorphismEmbedding
  exact ehnHomomorphismEmbedding_factor_full_side
    hPiece jLeft hContained

end AllThoseRamseyClasses.Lifts
