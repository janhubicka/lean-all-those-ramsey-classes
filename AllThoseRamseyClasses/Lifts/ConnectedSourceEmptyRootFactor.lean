import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor

/-!
# A reusable connected-source EHN factorization over an empty full root

A weak (possibly NONINJECTIVE) EHN homomorphism-embedding of a nonempty
Gaifman-connected native source into an actual full functional free
amalgam over an EMPTY full common root factors into one of its two
full native sides. The path step uses only the preserved positive
relations and complete original function incidences.

This is a source-specific lemma. It can be reused for named finite
forbidden families as well as arbitrary forbidden source predicates.
Nullary native symbols are allowed PROVIDED a genuine full empty
root of the specified amalgam already exists.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual EHN weak source map with connected, nonempty domain
cannot meet BOTH exclusive regions of an empty-root free amalgam.
It genuinely factors through a full side: the result is still an
EHN homomorphism-embedding, not just a weak positive homomorphism. -/
theorem connectedSourceEHN_factor_emptyFreeSide
    {U UX UA UB UT : Type} [IsEmpty UX]
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
    (hf : Source.IsEHNHomomorphismEmbedding D f) :
    (∃ g : U → UA, Source.IsEHNHomomorphismEmbedding A g) ∨
      (∃ g : U → UB, Source.IsEHNHomomorphismEmbedding B g) := by
  obtain ⟨base⟩ := hNonempty
  have hNoRoot (x : U) :
      x ∉ weakFreeRootPart (sL := iA) (iL := jA) f := by
    rintro ⟨r, _⟩
    exact isEmptyElim r
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
