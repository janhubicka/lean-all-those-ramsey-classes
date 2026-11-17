import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance

/-!
# Native EHN avoidance descends along weak maps and source free amalgams

This supplies the exact functional fact used by the relative-root
continuation repair: any allowed FULL amalgam of two rooted sides
makes their genuine native free amalgam forbidden-free.

It is critical to use a homomorphism-embedding, not a plain
homomorphism, and to preserve the complete native partial-function
structure on every irreducible source test. This is about the ORIGINAL
forbidden family F: there is no image-closure, regularity, source
minimization or finite-signature hypothesis.

The existence of an actual IsFreeAmalgam diagram is a premise.
This file does NOT construct its carrier and does NOT prove the
whole relative-continuation homogenization theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Forbidden-free classes defined by native EHN avoidance are
backward closed under ANY EHN map, not only full embeddings. -/
theorem avoidsGlobalFunctionalEHN_of_ehn
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VA VB : Type}
    {A : Structure L VA} {B : Structure L VB}
    (f : VA → VB)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hB : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F A := by
  intro U Source hFin hF g hg
  have hComp : Source.IsEHNHomomorphismEmbedding B (f ∘ g) :=
    hf.comp hg
  exact (hB Source hFin hF (f ∘ g)) hComp

/-- If the two sides of a genuine native functional free amalgam
have EHN maps into the same forbidden-free target agreeing on
their full root, the WHOLE free amalgam is forbidden-free.
In particular full target-side embeddings in an arbitrary allowed
amalgam can be used here, proving that free amalgamation is the
correct test for continuation incompatibility. -/
theorem avoidsGlobalFunctionalEHN_of_freeFold
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX VA VB VW VT : Type}
    {X : Structure L VX}
    {A : Structure L VA} {B : Structure L VB}
    {Whole : Structure L VW} {Target : Structure L VT}
    {sA : Structure.Embedding X A}
    {sB : Structure.Embedding X B}
    {iA : Structure.Embedding A Whole}
    {iB : Structure.Embedding B Whole}
    (hfree : Structure.IsFreeAmalgam sA sB iA iB)
    (pA : VA → VT) (pB : VB → VT)
    (hpA : A.IsEHNHomomorphismEmbedding Target pA)
    (hpB : B.IsEHNHomomorphismEmbedding Target pB)
    (hcompat : ∀ r : VX, pA (sA r) = pB (sB r))
    (hTarget : AvoidsGlobalFunctionalEHN F Target) :
    AvoidsGlobalFunctionalEHN F Whole := by
  let f : VW → VT :=
    compatibleFunctionalFold hfree pA pB hcompat
  have hf : Whole.IsEHNHomomorphismEmbedding Target f :=
    compatibleFunctionalFold_isEHNHomomorphismEmbedding
      hfree pA pB hcompat hpA hpB
  intro U Source hFin hForb g hg
  have hComp : Source.IsEHNHomomorphismEmbedding Target (f ∘ g) :=
    hf.comp hg
  exact (hTarget Source hFin hForb (f ∘ g)) hComp

end AllThoseRamseyClasses.Lifts
