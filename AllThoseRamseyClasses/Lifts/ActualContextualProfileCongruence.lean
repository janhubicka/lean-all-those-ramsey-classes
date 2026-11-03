import AllThoseRamseyClasses.Lifts.NestedFunctionalOuterTestForward
import AllThoseRamseyClasses.Lifts.NestedFunctionalInnerStage
import AllThoseRamseyClasses.Lifts.NestedFunctionalTestProfiles
import AllThoseRamseyClasses.Lifts.FunctionalNestedReassociationReverse
import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoProfileTransport

/-!
# Actual contextual congruence of complete rooted incompatibility profiles

This is the full algebraic interchange-of-gluing step needed in the
original Section 3 Claim 2.  Suppose an actual full native functional
source Mid is the free amalgam of M and T over an inner root Start.
The old outer root Root is fully embedded in the retained T side.
No nesting of Start and Root is assumed.

For EVERY rooted outer test P, the following existential forbidden
source conditions are equivalent:

  (Mid +_Root P) is forbidden
      iff
  (M +_Start (T +_Root P)) is forbidden.

All sides and overlap maps are ACTUAL full native functional diagrams,
with relation reflection and complete set-valued function fibres,
including constants.  The forward direction is supplied by the
verified nested-context extraction.  The converse:
* recovers Mid's actual two-side diagram inside a nested witness;
* uses converse reassociation to recover a literal outer free diagram;
* identifies that induced inner stage with the CHOSEN Mid by its
  full side-preserving isomorphism, not by a weak-map quotient;
* leaves the chosen forbidden witness whole source unchanged.

Consequently inner all-test diagram equivalence M ~ M' implies
the COMPLETE outer all-test diagram equivalence
  (M +_Start T) ~ (M' +_Start T)
over any outer root whose full embedding factors through T.

There is NO forbidden-family isomorphism-closure premise.  This is
an existential test/profile result, NOT an assertion that two
prescribed source structures have equal forbidden membership.

Geometric Claim 2 still needs to identify the actual transported
outer contexts with the proper minimal-separator rooted pieces,
requiring opposite complete generated-boundary equality (Track A),
and to establish local finite B-support descent (Track C).
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The exact converse of the outer-to-nested test construction:
an arbitrary actual forbidden FULL nested diagram produces a
forbidden outer diagram against the CHOSEN middle source Mid,
without assuming forbidden-family isomorphism closure.

The underlying forbidden source Whole is the SAME witness. -/
theorem forbiddenNestedFunctionalTest_to_outerActual
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M T C R : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (rT : Structure.Embedding Root Tstr)
    (P : FunctionalRootExtension Root)
    (hBad : forbiddenNestedFunctionalTestDiagram Start Root F
      ({ Carrier := M, str := Mstr, rootEmbedding := sM } :
        FunctionalRootExtension Start)
      ({ Carrier := T, str := Tstr, rootEmbedding := sT } :
        FunctionalRootExtension Start)
      rT P) :
    forbiddenFunctionalDiagram Root F
      ({ Carrier := C, str := Mid,
         rootEmbedding := iT.comp rT } : FunctionalRootExtension Root)
      P := by
  classical
  rcases hBad with ⟨E, Ext, jT, jP, hExt, hNested⟩
  rcases hNested with
    ⟨W, Whole, hForbidden, iMWhole, eExt, hRe⟩
  let K : Set W :=
    iMWhole '' (Set.univ : Set M) ∪ eExt '' (Set.range jT)
  obtain ⟨hK, kM, kT, hInner, hMval, hTval⟩ :=
    fullFunctionalFreeAmalgam_induce_innerStage hRe
  let Inner : Structure L K := Whole.induce K hK
  let inc : Structure.Embedding Inner Whole :=
    Structure.inclusion Whole K hK
  have hComp : inc.comp kM = iMWhole := by
    apply Structure.Embedding.ext
    intro m
    exact hMval m
  have hReInner : Structure.IsFreeAmalgam
      sM (jT.comp sT) (inc.comp kM) eExt := by
    simpa only [hComp] using hRe
  have heT (t : T) : eExt (jT t) = inc (kT t) :=
    (hTval t).symm
  have heP (p : P.Carrier) :
      eExt (jP p) = (eExt.comp jP) p := rfl
  have hOuterInner :
      Structure.IsFreeAmalgam
        (kT.comp rT) P.rootEmbedding inc (eExt.comp jP) :=
    fullFunctionalFreeAmalgam_reassociate_right_reverse
      hInner hExt eExt heT heP hReInner
  obtain ⟨e, heSurj, _heM, heRight⟩ :=
    freeAmalgamDiagram_unique hMid hInner
  have hRoot : ∀ r : R,
      e ((iT.comp rT) r) = (kT.comp rT) r := by
    intro r
    exact heRight (rT r)
  have hOuterChosen :
      Structure.IsFreeAmalgam
        (iT.comp rT) P.rootEmbedding
        (inc.comp e) (eExt.comp jP) :=
    freeAmalgam_precompose_left_iso
      hOuterInner e heSurj (iT.comp rT) hRoot
  exact ⟨W, Whole, hForbidden,
    inc.comp e, eExt.comp jP, hOuterChosen⟩

/-- Complete equivalence between a forbidden actual outer-root
test of a CHOSEN full source `Mid = M +_Start T` and its
two-stage existential nested test over the unchanged T side.

Every outer test P is admitted, with no assumption of forbidden
isomorphism closure, and no inclusion relation between roots. -/
theorem forbiddenOuterActual_iff_nestedFunctionalTest
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M T C R : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (rT : Structure.Embedding Root Tstr)
    (P : FunctionalRootExtension Root) :
    forbiddenFunctionalDiagram Root F
      ({ Carrier := C, str := Mid,
         rootEmbedding := iT.comp rT } : FunctionalRootExtension Root)
      P ↔
    forbiddenNestedFunctionalTestDiagram Start Root F
      ({ Carrier := M, str := Mstr,
         rootEmbedding := sM } : FunctionalRootExtension Start)
      ({ Carrier := T, str := Tstr,
         rootEmbedding := sT } : FunctionalRootExtension Start)
      rT P := by
  constructor
  · rintro ⟨W, Whole, hForbidden, iMidWhole, iPWhole, hOuter⟩
    obtain ⟨E, Ext, jT, jP, hExt, hNested⟩ :=
      forbiddenOuterFunctionalDiagram_to_nestedTest
        F hMid hOuter hForbidden
    exact ⟨E, Ext, jT, jP, hExt, hNested⟩
  · exact forbiddenNestedFunctionalTest_to_outerActual
      F hMid rT P

/-- Section 3's full native **contextual congruence**, at the
level of complete existential rooted forbidden diagrams.

If M and M' have identical tests over the FULL inner Start root,
their CHOSEN actual free-amalgam extensions by a fixed T have
identical tests over ANY full outer Root embedded in T.

This theorem does not rely on isomorphism closure of F and does
not ask the two roots to be nested. It is not a theorem about
geometric minimal separators until that separate predicate
is verified for the chosen outer contexts. -/
theorem functionalActualContext_profile_equiv_of_inner_equiv
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M M' T C C' R : Type}
    {Start : Structure L S}
    {Mstr : Structure L M}
    {M'str : Structure L M'}
    {Tstr : Structure L T}
    {Mid : Structure L C} {Mid' : Structure L C'}
    {Root : Structure L R}
    {sM : Structure.Embedding Start Mstr}
    {sM' : Structure.Embedding Start M'str}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {jM : Structure.Embedding M'str Mid'}
    {jT : Structure.Embedding Tstr Mid'}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (hMid' : Structure.IsFreeAmalgam sM' sT jM jT)
    (rT : Structure.Embedding Root Tstr)
    (hEq : (functionalDiagramPieceSetoid Start F).r
      ({ Carrier := M, str := Mstr,
         rootEmbedding := sM } : FunctionalRootExtension Start)
      ({ Carrier := M', str := M'str,
         rootEmbedding := sM' } : FunctionalRootExtension Start)) :
    (functionalDiagramPieceSetoid Root F).r
      ({ Carrier := C, str := Mid,
         rootEmbedding := iT.comp rT } : FunctionalRootExtension Root)
      ({ Carrier := C', str := Mid',
         rootEmbedding := jT.comp rT } : FunctionalRootExtension Root) := by
  apply (functionalDiagramPiece_equiv_iff Root F
    ({ Carrier := C, str := Mid,
       rootEmbedding := iT.comp rT } : FunctionalRootExtension Root)
    ({ Carrier := C', str := Mid',
       rootEmbedding := jT.comp rT } :
      FunctionalRootExtension Root)).mpr
  intro P
  calc
    forbiddenFunctionalDiagram Root F
      ({ Carrier := C, str := Mid,
         rootEmbedding := iT.comp rT } :
        FunctionalRootExtension Root) P
      ↔ forbiddenNestedFunctionalTestDiagram Start Root F
          ({ Carrier := M, str := Mstr,
             rootEmbedding := sM } : FunctionalRootExtension Start)
          ({ Carrier := T, str := Tstr,
             rootEmbedding := sT } : FunctionalRootExtension Start)
          rT P :=
        forbiddenOuterActual_iff_nestedFunctionalTest F hMid rT P
    _ ↔ forbiddenNestedFunctionalTestDiagram Start Root F
          ({ Carrier := M', str := M'str,
             rootEmbedding := sM' } : FunctionalRootExtension Start)
          ({ Carrier := T, str := Tstr,
             rootEmbedding := sT } : FunctionalRootExtension Start)
          rT P :=
        forbiddenNestedFunctionalTestDiagram_iff_of_inner_equiv
          Start Root F
          ({ Carrier := M, str := Mstr,
             rootEmbedding := sM } : FunctionalRootExtension Start)
          ({ Carrier := M', str := M'str,
             rootEmbedding := sM' } : FunctionalRootExtension Start)
          ({ Carrier := T, str := Tstr,
             rootEmbedding := sT } : FunctionalRootExtension Start)
          rT hEq P
    _ ↔ forbiddenFunctionalDiagram Root F
          ({ Carrier := C', str := Mid',
             rootEmbedding := jT.comp rT } :
            FunctionalRootExtension Root) P :=
        (forbiddenOuterActual_iff_nestedFunctionalTest
          F hMid' rT P).symm

end AllThoseRamseyClasses.Lifts
