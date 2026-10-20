import AllThoseRamseyClasses.Lifts.GlobalConnectedForbiddenJEP
import AllThoseRamseyClasses.Lifts.ConnectedEHNRootAvoidance

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
