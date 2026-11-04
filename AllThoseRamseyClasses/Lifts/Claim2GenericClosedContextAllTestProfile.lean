import AllThoseRamseyClasses.Lifts.ActualContextualProfileCongruence
import AllThoseRamseyClasses.Lifts.NamedNestedFunctionalContext

/-!
# Track C: all rooted forbidden tests survive replacement inside ANY closed context

The already verified contextual incongruence proof in the original
2019 native functional-language lift is generic: for an ACTUAL
two-step free-amalgam diagram, replacing an inner rooted piece
by an equivalently incompatible rooted piece preserves ALL
forbidden outer-rooted tests.

The earlier application to Section 3 Claim 2 was stated only
for a genuine OLD outer geometric minimal-cut piece P, because
P supplied the closed retained complement subset SR and the
factorization of its ordered full root through the complement.

Neither P's minimal-separator property nor P's selected-component
geometry enters the actual nested test reassociation. The
following theorem abstracts the proof in the precise reusable
form:

 Old = OldInner +_Start E,
 New = NewInner +_Start E,
 SR ⊆ E is function-closed and contains the full Start root,
 KOld = iOldInner(OldInner) ∪ iOldE(SR),
 KNew = iNewInner(NewInner) ∪ iNewE(SR).

ANY fully embedded outer root RootOuter of E|SR is therefore
fully embedded in both KOld and KNew. If the two inner
extensions have the same complete forbidden-test diagram
profile over Start, then these ACTUAL induced native
contexts have identical ALL forbidden rooted profiles over
RootOuter. The root coordinates are exactly the corresponding
old/new full complement vertices.

No assumption that KOld or KNew is a genuine geometric
minimal-separator piece, no homomorphism image quotient, no
intermediate A-source minimality, no injective weak EHN map
and no isomorphism-closure assumption on the original family.
This is the generic algebraic bridge for the alternate
closed/no-escape contextual iteration.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Arbitrary genuine FULL native functional source diagrams with
the same complete retained complement and diagram-equivalent
inner pieces have the SAME ALL-TEST forbidden incompatibility
profile on ANY outer full root in a closed complement context.

This is about genuine induced closed CONTEXTS, not an assertion
that either context is a selected geometric minimal separator. -/
theorem fullFreeAmalgam_closedContext_allTestProfile_equiv
    (F : ∀ {Z : Type v}, Structure L Z → Prop)
    {H A A' E V W R : Type v}
    {Start : Structure L H}
    {OldInner : Structure L A}
    {NewInner : Structure L A'}
    {Estr : Structure L E}
    {Old : Structure L V}
    {New : Structure L W}
    {sOldL : Structure.Embedding Start OldInner}
    {sNewL : Structure.Embedding Start NewInner}
    {sE : Structure.Embedding Start Estr}
    {iOldL : Structure.Embedding OldInner Old}
    {iOldE : Structure.Embedding Estr Old}
    {iNewL : Structure.Embedding NewInner New}
    {iNewE : Structure.Embedding Estr New}
    (hOldFree : Structure.IsFreeAmalgam sOldL sE iOldL iOldE)
    (hNewFree : Structure.IsFreeAmalgam sNewL sE iNewL iNewE)
    (SR : Set E) (hSRclosed : Estr.IsClosed SR)
    (hRootSR : ∀ r : H, sE r ∈ SR)
    (RootOuter : Structure L R)
    (rE : Structure.Embedding RootOuter
      (Estr.induce SR hSRclosed))
    (hInnerEq : (functionalDiagramPieceSetoid Start F).r
      ({ Carrier := A, str := OldInner,
         rootEmbedding := sOldL } : FunctionalRootExtension Start)
      ({ Carrier := A', str := NewInner,
         rootEmbedding := sNewL } : FunctionalRootExtension Start)) :
    let KOld : Set V :=
      iOldL '' (Set.univ : Set A) ∪ iOldE '' SR
    let KNew : Set W :=
      iNewL '' (Set.univ : Set A') ∪ iNewE '' SR
    ∃ (hKOld : Old.IsClosed KOld)
      (hKNew : New.IsClosed KNew)
      (rootOld : Structure.Embedding RootOuter
        (Old.induce KOld hKOld))
      (rootNew : Structure.Embedding RootOuter
        (New.induce KNew hKNew)),
      (functionalDiagramPieceSetoid RootOuter F).r
        ({ Carrier := KOld, str := Old.induce KOld hKOld,
           rootEmbedding := rootOld } : FunctionalRootExtension RootOuter)
        ({ Carrier := KNew, str := New.induce KNew hKNew,
           rootEmbedding := rootNew } : FunctionalRootExtension RootOuter) ∧
      (∀ r : R, (rootOld r).1 = iOldE ((rE r).1)) ∧
      (∀ r : R, (rootNew r).1 = iNewE ((rE r).1)) := by
  classical
  obtain ⟨hKOld, oldS, jOldL, jOldE,
      hOldCtx, _hOldLcoords, hOldEcoords, hOldScoords⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hOldFree SR hSRclosed hRootSR
  obtain ⟨hKNew, newS, jNewL, jNewE,
      hNewCtx, _hNewLcoords, hNewEcoords, hNewScoords⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hNewFree SR hSRclosed hRootSR
  have hSameS : oldS = newS := by
    apply Structure.Embedding.ext
    intro r
    apply Subtype.ext
    calc
      (oldS r).1 = sE r := hOldScoords r
      _ = (newS r).1 := (hNewScoords r).symm
  have hNewCtx' :
      Structure.IsFreeAmalgam sNewL oldS jNewL jNewE := by
    simpa only [← hSameS] using hNewCtx
  have hProfiles :
      (functionalDiagramPieceSetoid RootOuter F).r
        ({ Carrier := _, str := Old.induce _ hKOld,
           rootEmbedding := jOldE.comp rE } :
          FunctionalRootExtension RootOuter)
        ({ Carrier := _, str := New.induce _ hKNew,
           rootEmbedding := jNewE.comp rE } :
          FunctionalRootExtension RootOuter) :=
    functionalActualContext_profile_equiv_of_inner_equiv
      F hOldCtx hNewCtx' rE hInnerEq
  refine ⟨hKOld, hKNew,
    jOldE.comp rE, jNewE.comp rE, hProfiles, ?_, ?_⟩
  · intro r
    exact hOldEcoords (rE r)
  · intro r
    exact hNewEcoords (rE r)

end AllThoseRamseyClasses.Lifts
