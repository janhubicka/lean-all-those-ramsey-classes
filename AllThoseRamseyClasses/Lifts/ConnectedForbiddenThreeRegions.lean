import AllThoseRamseyClasses.Lifts.ConnectedWitnessRootIntersection

/-!
# A connected forbidden weak witness has all three source regions

Let D be a genuine FULL native functional free amalgam A ⊕_X B,
with A and B both forbidden-free for some connected forbidden family.
If a weak EHN map f from one of the forbidden sources exists in D,
then its SOURCE vertices must map to each of the three regions:

* exclusively into A outside X;
* exclusively into B outside X;
* into the shared full root X.

The two exclusive regions must be nonempty even WITHOUT source
connectedness: otherwise the map factors through the other side by
the verified EHN cancellation for full embeddings. Connectedness is
needed for the third nonemptiness, via the separate root-intersection
lemma. The common-root preimage is function-closed and separates the
two exclusive regions by true source Gaifman paths.

This certifies the entire initial three-way partition of the
printed Section 3 strong-amalgamation proof without any assumption
that the weak forbidden-source map is injective. It does NOT make
the image of a smaller minimal separating root injective, nor
validate the remaining Claim 1/Claim 2 flip induction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If the source has no EHN map into EITHER full side, then an
arbitrary EHN witness in their actual free amalgam has at least
one source vertex in each EXCLUSIVE side. This is independent of
source connectedness, forbidden-family regularity and injectivity. -/
theorem ehnWitness_bothExclusiveRegions_nonempty
    {U UX UA UB UT : Type}
    (Source : Structure L U)
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
    (∃ x : U,
      x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f) ∧
    (∃ y : U,
      y ∈ weakFreeRightPart
        (sL := iA) (iL := jA) (iR := jB) f) := by
  constructor
  · by_contra hNoLeft
    have hNoL (x : U) :
        x ∉ weakFreeLeftPart (sL := iA) (iL := jA) f := by
      intro hx
      exact hNoLeft ⟨x, hx⟩
    have hRange : ∀ x : U, ∃ b : UB, f x = jB b := by
      intro x
      rcases weakFreePartition_covers hFree f x with
        hRoot | hLeft | hRight
      · obtain ⟨r, hr⟩ := hRoot
        refine ⟨iB r, ?_⟩
        calc
          f x = jA (iA r) := hr.symm
          _ = jB (iB r) :=
            (hFree.overlap (iA r) (iB r)).mpr
              ⟨r, rfl, rfl⟩
      · exact False.elim (hNoL x hLeft)
      · obtain ⟨⟨b, hb⟩, _⟩ := hRight
        exact ⟨b, hb⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jB hRange
    exact hB g hg
  · by_contra hNoRight
    have hNoR (x : U) :
        x ∉ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f := by
      intro hx
      exact hNoRight ⟨x, hx⟩
    have hRange : ∀ x : U, ∃ a : UA, f x = jA a := by
      intro x
      rcases weakFreePartition_covers hFree f x with
        hRoot | hLeft | hRight
      · obtain ⟨r, hr⟩ := hRoot
        exact ⟨iA r, hr.symm⟩
      · obtain ⟨⟨a, ha⟩, _⟩ := hLeft
        exact ⟨a, ha⟩
      · exact False.elim (hNoR x hRight)
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jA hRange
    exact hA g hg

/-- Exact initial data for an alleged connected forbidden-source
witness in a FULL free amalgam of two forbidden-free sides.
All three source regions are inhabited, the full common-root
preimage is function-closed, and that preimage separates EVERY
exclusive left vertex from EVERY exclusive right vertex.

No injective forbidden-witness reduction is used; in particular
this proof remains valid when several source root vertices have
one target image in the shared root. -/
theorem globalForbiddenConnectedWitness_threeRegions
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
    Source.IsClosed
        (weakFreeRootPart (sL := iA) (iL := jA) f) ∧
      (∃ x : U,
        x ∈ weakFreeRootPart (sL := iA) (iL := jA) f) ∧
      (∃ x : U,
        x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f) ∧
      (∃ y : U,
        y ∈ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f) ∧
      (∀ (x y : U)
        (hx : x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f)
        (hy : y ∈ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f),
        ¬ ReachOutside Source.graph
          (weakFreeRootPart (sL := iA) (iL := jA) f)
          ⟨x, hx.2⟩ ⟨y, hy.2⟩) := by
  have hClosed : Source.IsClosed
      (weakFreeRootPart (sL := iA) (iL := jA) f) :=
    weakFreeRootPart_isClosed (sL := iA) (iL := jA) f hf.1
  obtain ⟨xRoot, r, hr⟩ :=
    globalConnectedForbiddenWitness_meets_sharedRoot
      F hConnected hFree hA hB Source hFin hF f hf
  have hRoot :
      xRoot ∈ weakFreeRootPart (sL := iA) (iL := jA) f :=
    ⟨r, hr.symm⟩
  obtain ⟨hLeft, hRight⟩ :=
    ehnWitness_bothExclusiveRegions_nonempty
      Source X A B D iA iB jA jB hFree
      (hA Source hFin hF) (hB Source hFin hF) f hf
  refine ⟨hClosed, ⟨xRoot, hRoot⟩, hLeft, hRight, ?_⟩
  intro x y hx hy
  exact weakFreePartition_root_separates_exclusive
    hFree f hf.1 hx hy

end AllThoseRamseyClasses.Lifts
