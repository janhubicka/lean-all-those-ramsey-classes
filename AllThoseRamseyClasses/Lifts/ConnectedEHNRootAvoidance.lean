import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor

/-!
# Generic connected EHN full-side factorization away from a common root

A nonempty connected weak EHN witness in a genuine native functional
free amalgam cannot meet both exclusive sides without meeting the
common FULL root. In the root-avoiding case the entire map factors
through one FULL side, even when the original weak map is noninjective.

This is the minimal reusable source-specific theorem. The original
global forbidden-free and finite-family folded applications should
not replay the Gaifman path argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If a nonempty Gaifman-connected original source has an EHN weak
map into an actual FULL native functional free amalgam and the map
avoids the common root, the whole map factors as an EHN
homomorphism-embedding into one of the two FULL sides.

This is valid for arbitrary (possibly noninjective) weak source
maps and nonempty common roots; unlike the empty-root special case,
the explicit root-avoidance hypothesis is indispensable. -/
theorem connectedEHN_factor_fullSide_of_avoidsRoot
    {U UX UA UB UT : Type}
    (Source : Structure L U)
    (hNonempty : Nonempty U)
    (hConnected : ∀ x y : U,
      Relation.ReflTransGen (GaifmanAdjacent Source.graph) x y)
    (X : Structure L UX)
    (A : Structure L UA) (B : Structure L UB)
    (D : Structure L UT)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (jA : Structure.Embedding A D)
    (jB : Structure.Embedding B D)
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (f : U → UT)
    (hf : Source.IsEHNHomomorphismEmbedding D f)
    (hNoRoot : ∀ x : U,
      x ∉ weakFreeRootPart (sL := iA) (iL := jA) f) :
    (∃ g : U → UA, Source.IsEHNHomomorphismEmbedding A g) ∨
      (∃ g : U → UB, Source.IsEHNHomomorphismEmbedding B g) := by
  obtain ⟨base⟩ := hNonempty
  rcases weakFreePartition_covers hFree f base with
    hRoot | hLeft | hRight
  · exact False.elim (hNoRoot base hRoot)
  · have hAllLeft (x : U) :
        x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f := by
      have hPath := hConnected base x
      induction hPath with
      | refl => exact hLeft
      | @tail a b hab hedge ih =>
          exact weakFreePartition_left_step
            hFree f hf.1 ih (hNoRoot b) hedge
    have hRange : ∀ x : U, ∃ a : UA, f x = jA a := by
      intro x
      obtain ⟨⟨a, ha⟩, _⟩ := hAllLeft x
      exact ⟨a, ha⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jA hRange
    exact Or.inl ⟨g, hg⟩
  · have hAllRight (x : U) :
        x ∈ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f := by
      have hPath := hConnected base x
      induction hPath with
      | refl => exact hRight
      | @tail a b hab hedge ih =>
          exact weakFreePartition_right_step
            hFree f hf.1 ih (hNoRoot b) hedge
    have hRange : ∀ x : U, ∃ b : UB, f x = jB b := by
      intro x
      obtain ⟨⟨b, hb⟩, _⟩ := hAllRight x
      exact ⟨b, hb⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jB hRange
    exact Or.inr ⟨g, hg⟩


end AllThoseRamseyClasses.Lifts
