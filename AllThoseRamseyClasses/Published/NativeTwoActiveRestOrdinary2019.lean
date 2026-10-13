import AllThoseRamseyClasses.Published.NativeActiveCommonWeakCollision2019

/-!
# Ordinary old-Picture maps on BOTH RESTs of two source-active native HJ copies

The true simultaneous native attachment has a valid copy/rest free cover.
For two different active private copy indices i,j, another valid free
source split uses the TWO REST pieces Rest(j) and Rest(i); all core
vertices belong to both pieces. That free-cover theorem is in the
separate NativeTwoRestFree2019 module.

We prove the OLD MAPS of those two REST source pieces without assuming
their root is an induced A-copy.

Assume the ORIGINAL source has private-active attached copy indices
contained in {i,j}. The left rest excludes the private exterior of j,
so every private-active line of that restricted source is i. Choose
the genuine parameter coordinate of line i; the existing checked
active-subhistory coordinate fold gives an ORDINARY
homomorphism-embedding of this whole exact rest into Old.

The right rest likewise has only private-active index j, and its
own parameter coordinate gives another ordinary old-Picture map.

No parameter coordinate common to the two different lines is required.
The full source's native map may be globally NONINJECTIVE. The weak
rest sources are not assumed U-closed; the native target may be
non-semi-closed. The maps are ordinarily reflective on irreducibles.

The common REST intersection includes all source vertices mapping
into the ENTIRE power core. Their two coordinate evaluations can
have the same part but fail to factor through TWO full embedded
A-copies with ONE root map. Thus the exact missing higher-rank step
is genuine vertex-level CLOSED K-ROOT COMPATIBILITY, not existence
of ordinary side maps in the two-active-copy case.

This file does NOT claim Lemma 2.30 or corrected Theorem 2.18.
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

/-- When the only original source-private-active HJ copy indices
are i and j, EACH complementary REST has a genuine ORDINARY
homomorphism-embedding to the previous Old Picture. The two
embeddings can use DIFFERENT parameter coordinates k_i and k_j.

The exact weak REST vertex sets contain the full tested core.
No common A-root factorization is asserted or assumed. -/
theorem native2019_two_only_active_rest_ordinary_old_maps
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
    (i j : I) (hij : i ≠ j)
    (hOnly : ∀ k : I,
      (∃ x : U, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x)) →
        k = i ∨ k = j) :
    let Left : Set U :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) j (p x)}
    let Right : Set U :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)}
    ∃ (pLeft : Left → V) (pRight : Right → V),
      (Source.induce Left).IsHomomorphismEmbedding
        Old.toRelStructure pLeft ∧
      (Source.induce Right).IsHomomorphismEmbedding
        Old.toRelStructure pRight := by
  classical
  let Left : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x)}
  let Right : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  obtain ⟨ki, hki⟩ := (lines i).hasParameter
  obtain ⟨kj, hkj⟩ := (lines j).hasParameter
  have hLeftOrd :
      (Source.induce Left).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines))
        (fun x : Left => p x.1) :=
    hp.comp (inclusion Source Left).isHomomorphismEmbedding
  have hLeftCommon : ∀ k : I,
      (∃ x : Left, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x.1)) →
      (lines k).symbol ki = .parameter := by
    intro k ⟨x, hx⟩
    rcases hOnly k ⟨x.1, hx⟩ with hki' | hkj'
    · subst k
      exact hki
    · subst k
      exact False.elim (x.2 hx)
  obtain ⟨fL, hfL⟩ :=
    native2019_actual_active_common_coordinate_old_ordinary
      (Source.induce Left) Old alpha A hRestricted lines
      (fun x : Left => p x.1) hLeftOrd ki hLeftCommon
  have hRightOrd :
      (Source.induce Right).IsHomomorphismEmbedding
        (attach Old.toRelStructure (Old.support alpha)
          (power (Old.restrict alpha) N).toRelStructure
          (closureLineMaps Old alpha A hRestricted lines))
        (fun x : Right => p x.1) :=
    hp.comp (inclusion Source Right).isHomomorphismEmbedding
  have hRightCommon : ∀ k : I,
      (∃ x : Right, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x.1)) →
      (lines k).symbol kj = .parameter := by
    intro k ⟨x, hx⟩
    rcases hOnly k ⟨x.1, hx⟩ with hki' | hkj'
    · subst k
      exact False.elim (x.2 hx)
    · subst k
      exact hkj
  obtain ⟨fR, hfR⟩ :=
    native2019_actual_active_common_coordinate_old_ordinary
      (Source.induce Right) Old alpha A hRestricted lines
      (fun x : Right => p x.1) hRightOrd kj hRightCommon
  exact ⟨fL, fR, hfL, hfR⟩

/-- A source vertex lying in BOTH distinct complementary REST pieces
has its actual native image in the POWER CORE, provided no exterior
indices except the two selected i,j are source-active.

The common root can thus be large and contain arbitrary core vertices,
not merely the image of one A-word line intersection. -/
theorem native2019_two_only_active_rest_root_in_core
    {V W U I : Type v}
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I))
    (i j : I) (hij : i ≠ j)
    (hOnly : ∀ k : I,
      (∃ x : U, OutsideAt
        (W := W) (I := I) Support k (p x)) →
        k = i ∨ k = j)
    (x : U)
    (hRestJ : ¬ OutsideAt (W := W) (I := I) Support j (p x))
    (hRestI : ¬ OutsideAt (W := W) (I := I) Support i (p x)) :
    ∃ w : W, p x = Sum.inl w := by
  cases hx : p x with
  | inl w =>
      exact ⟨w, rfl⟩
  | inr z =>
      rcases z with ⟨k, y⟩
      have hz : OutsideAt (W := W) (I := I) Support k (p x) :=
        ⟨y, hx⟩
      rcases hOnly k ⟨x, hz⟩ with hi | hj
      · subst k
        exact False.elim (hRestI hz)
      · subst k
        exact False.elim (hRestJ hz)

end AllThoseRamseyClasses.Published
