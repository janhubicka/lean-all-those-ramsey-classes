import AllThoseRamseyClasses.Lifts.GlobalConnectedForbiddenJEP

/-!
# Connected weak EHN witnesses must meet an amalgamation root

An irreducible forbidden source embeds FULLY and belongs to one side
of a native functional free amalgam. A merely connected source need
not do so: its image may visit both exclusive sides through the
common FULL root, even if the weak EHN map identifies source vertices.

But a nonempty connected source whose weak EHN image avoids the
common root still factors into one FULL target side. This follows
from positive-incidence preservation and the verified exact
three-part partition of arbitrary weak sources, not from an invalid
injectivization of source maps.

Consequently, whenever each free-amalgam side excludes an EHN
witness from the connected source, EVERY weak source witness into
the amalgam must actually hit the common FULL root.

This is a general-source invariant (with no forbidden-family
regularity, closure-under-images, finite-carrier or root-injectivity
hypothesis), useful at the start of the Section 3 separator analysis.
It does NOT show that the image of the entire separating root is
injective, nor establish the still-open global piece shadow
avoidance/strong-amalgamation lemma.
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

/-- If neither FULL side admits any EHN witness of the connected
source, then EVERY EHN source witness into their actual free
amalgam must hit the common root. The image may be noninjective;
the conclusion does not assert more than genuine root incidence. -/
theorem connectedEHNWitness_meets_sharedRoot
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
    (hA : ∀ g : U → UA,
      ¬ Source.IsEHNHomomorphismEmbedding A g)
    (hB : ∀ g : U → UB,
      ¬ Source.IsEHNHomomorphismEmbedding B g)
    (f : U → UT)
    (hf : Source.IsEHNHomomorphismEmbedding D f) :
    ∃ x : U, ∃ r : UX, f x = jA (iA r) := by
  by_contra hNone
  have hNoRoot (x : U) :
      x ∉ weakFreeRootPart (sL := iA) (iL := jA) f := by
    rintro ⟨r, hr⟩
    apply hNone
    exact ⟨x, r, hr.symm⟩
  rcases connectedEHN_factor_fullSide_of_avoidsRoot
      Source hNonempty hConnected X A B D
      iA iB jA jB hFree f hf hNoRoot with
    ⟨g, hg⟩ | ⟨g, hg⟩
  · exact hA g hg
  · exact hB g hg

/-- Applied to the original regular/global forbidden-family
semantics: every forbidden connected source witness in a free
amalgam of two forbidden-free native witnesses hits the shared
full old root. This makes the source separator preimage
NONEMPTY, but does not prove root-image injectivity. -/
theorem globalConnectedForbiddenWitness_meets_sharedRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    {D : Structure L UT}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    {jA : Structure.Embedding A D}
    {jB : Structure.Embedding B D}
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (hA : AvoidsGlobalFunctionalEHN F A)
    (hB : AvoidsGlobalFunctionalEHN F B)
    {U : Type} (Source : Structure L U)
    (hFin : Finite U) (hF : F Source)
    (f : U → UT)
    (hf : Source.IsEHNHomomorphismEmbedding D f) :
    ∃ x : U, ∃ r : UX, f x = jA (iA r) := by
  have hc := hConnected Source hFin hF
  exact connectedEHNWitness_meets_sharedRoot
    Source hc.1 hc.2 X A B D iA iB jA jB hFree
    (hA Source hFin hF) (hB Source hFin hF) f hf

end AllThoseRamseyClasses.Lifts
