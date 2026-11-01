import AllThoseRamseyClasses.Lifts.ActualContextualProfileCongruence
import AllThoseRamseyClasses.Lifts.NamedNestedFunctionalContext
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Geometric source-context specialization of full profile congruence

This is the precise application of the generic all-test congruence
to an inner replacement Q in an ACTUAL geometric functional source.

Old = Inner +_U E is the genuine original free source diagram
at an inner minimal separator U. Let P be an old outer piece,
and suppose every inner root vertex lies inside P. Let
S = E ∩ P be the retained FUNCTION-CLOSED part of E.
Then the old and new transported contexts both carry genuine
native full diagrams:
  OldContext = Inner +_U (E|S),
  NewContext = Q     +_U (E|S).

If Inner and Q are equivalent for ALL U-rooted forbidden tests,
the contexts have the same ALL outer-root tests for ANY full outer
root embedding `RootOuter -> E|S`. Both actual contexts and their
full embeddings are CONSTRUCTED here: no contextual diagram
hypothesis is added.

This is a theorem about exactly the induced transported CONTEXT,
not yet the genuine geometric outer minimal-cut piece. To identify
this context with the selected component of the new source on the
old outer root, Track A must still prove the opposite generated
boundary and minimal closed separator. The exact old outer root
factorization is handled independently in the retained-root module.

No isomorphism closure of F, no weak map injection, and no relation
between the inner and outer roots is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual functional inner-source replacement by a
diagram-equivalent Q preserves the COMPLETE forbidden
incompatibility profiles of the old and new closed transported
outer contexts, at ANY full outer root already embedded in
the retained exact complement.

The resulting old and new carriers are induced subtypes of
the ORIGINAL and REPLACEMENT SOURCE, respectively, not
unnamed existential pushouts. -/
theorem geometricOuterContext_profile_equiv_after_innerReplacement
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W R : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hEq : (functionalDiagramPieceSetoid
        (geometricGlobalFunctionalChart Old d).root F).r
      (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (RootOuter : Structure L R)
    (rT : Structure.Embedding RootOuter
      ((geometricGlobalComplementChart Old d).str.induce
        (oldOuterContextInInnerComplement Old P d)
        (oldOuterContextInInnerComplement_isClosed Old P d))) :
    let E := geometricGlobalComplementChart Old d
    let S := oldOuterContextInInnerComplement Old P d
    let iOldQ : Structure.Embedding
        (geometricGlobalFunctionalChart Old d).ext.str Old :=
      functionalComponentEmbedding Old (Set.range d.roots)
        d.minimal.1 d.left
    let iOldE : Structure.Embedding E.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    let OldK : Set V :=
      iOldQ '' (Set.univ : Set
        (geometricGlobalFunctionalChart Old d).ext.Carrier) ∪ iOldE '' S
    let NewK : Set W :=
      iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' S
    ∃ (hOldK : Old.IsClosed OldK) (hNewK : New.IsClosed NewK)
      (oldRoot : Structure.Embedding RootOuter (Old.induce OldK hOldK))
      (newRoot : Structure.Embedding RootOuter (New.induce NewK hNewK)),
      (functionalDiagramPieceSetoid RootOuter F).r
        ({ Carrier := OldK, str := Old.induce OldK hOldK,
           rootEmbedding := oldRoot } : FunctionalRootExtension RootOuter)
        ({ Carrier := NewK, str := New.induce NewK hNewK,
           rootEmbedding := newRoot } : FunctionalRootExtension RootOuter) := by
  classical
  let E := geometricGlobalComplementChart Old d
  let S := oldOuterContextInInnerComplement Old P d
  have hS : E.str.IsClosed S :=
    oldOuterContextInInnerComplement_isClosed Old P d
  let Inner := (geometricGlobalFunctionalChart Old d).ext
  let iOldQ : Structure.Embedding Inner.str Old :=
    functionalComponentEmbedding Old (Set.range d.roots)
      d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  have hOldFree :
      Structure.IsFreeAmalgam Inner.rootEmbedding E.rootEmbedding
        iOldQ iOldE :=
    geometricGlobalSource_freeDiagram Old d
  have hRootInS : ∀ r : Fin m, E.rootEmbedding r ∈ S :=
    oldOuterContext_contains_innerRoot Old P d hInnerRoot
  obtain ⟨hOldK, oldS, jOldQ, jOldT,
      hOldCtx, _hOldQval, _hOldTval, hOldSval⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hOldFree S hS hRootInS
  obtain ⟨hNewK, newS, jNewQ, jNewT,
      hNewCtx, _hNewQval, _hNewTval, hNewSval⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hFree S hS hRootInS
  have hSameS : oldS = newS := by
    apply Structure.Embedding.ext
    intro r
    apply Subtype.ext
    calc
      (oldS r).1 = E.rootEmbedding r := hOldSval r
      _ = (newS r).1 := (hNewSval r).symm
  have hNewCtx' :
      Structure.IsFreeAmalgam Q.rootEmbedding oldS jNewQ jNewT := by
    simpa only [← hSameS] using hNewCtx
  have hProfiles :
      (functionalDiagramPieceSetoid RootOuter F).r
        ({ Carrier := _, str := Old.induce _ hOldK,
           rootEmbedding := jOldT.comp rT } :
          FunctionalRootExtension RootOuter)
        ({ Carrier := _, str := New.induce _ hNewK,
           rootEmbedding := jNewT.comp rT } :
          FunctionalRootExtension RootOuter) :=
    functionalActualContext_profile_equiv_of_inner_equiv
      F hOldCtx hNewCtx' rT hEq
  exact ⟨hOldK, hNewK,
    jOldT.comp rT, jNewT.comp rT, hProfiles⟩

end AllThoseRamseyClasses.Lifts
