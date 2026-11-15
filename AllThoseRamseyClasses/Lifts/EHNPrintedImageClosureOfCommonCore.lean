import AllThoseRamseyClasses.Lifts.EHNPrintedTupleImageClosure

/-!
# A common forbidden full core forces printed EHN image closure

This is the mechanism behind the unary-marked enhancement of the
nonregular-saturation counterexample. Every source has a FULL copy
of one common forbidden structure Core (a marked singleton in that
example). The EHN property of maps FROM Core forces those images
to embed FULLY in the target (trivial for a full irreducible
singleton).

The resulting forbidden full substructure exists under an arbitrary
original-partial EHN map, without even requesting tuple-surjectivity.
We deliberately express the needed Core image-fullness property as
an explicit hypothesis. The separate finite marked graph source
family has not yet been fully instantiated in native Lean, and no
such instance is claimed here.

This theorem has the exact paper-shaped output
HasTupleSurjectiveForbiddenImageClosure F, not a stronger false
claim that the entire EHN image is isomorphic to some member F.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Printed tuple-surjective forbidden image closure follows
from a common forbidden FULL core and full-image reflection
for each EHN map starting at that core.

For example, in a two-binary-plus-unary signature let Core be
a one-vertex marked structure with no loops. A singleton is
irreducible, so every EHN map out of Core is a full embedding.
This is the mechanism for the independent infinite regular
marked family counterexample. -/
theorem hasTupleSurjectiveForbiddenImageClosure_of_commonFullCore
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VP : Type} (Core : Structure L VP)
    (hCoreForbidden : F Core)
    (hEveryHasCore :
      ∀ {V : Type} (Source : Structure L V),
        F Source → Nonempty (Structure.Embedding Core Source))
    (hCoreEHNfull :
      ∀ {Y : Type} (Target : Structure L Y) (f : VP → Y),
        Core.IsEHNHomomorphismEmbedding Target f →
          Nonempty (Structure.Embedding Core Target)) :
    HasTupleSurjectiveForbiddenImageClosure F := by
  intro X Y Source Target q hSource hOriginal _hTuple
  obtain ⟨e⟩ := hEveryHasCore Source hSource
  have hComposed :
      Core.IsEHNHomomorphismEmbedding Target (q ∘ e) :=
    hOriginal.toEHN.comp e.isEHNHomomorphismEmbedding
  obtain ⟨g⟩ := hCoreEHNfull Target (q ∘ e) hComposed
  exact ⟨VP, Core, hCoreForbidden, ⟨g⟩⟩

end AllThoseRamseyClasses.Lifts
