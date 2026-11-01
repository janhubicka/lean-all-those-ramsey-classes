import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredTagNormal
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedCoveredOldLaws
import PartiteConstruction.Functional.WholeMaskCoveredOutputCrossPattern2019
import PartiteConstruction.Functional.WholeMaskValueCoherenceHereditary2019

/-!
# Track C: genuine function-value coherence from actual corrected (4b)

The corrected clause (4b) places every U-closed U-irreducible exact
induced structure into the canonical image K(H). Previous Track C
lemmas derive, with NO fixed B, OLD output-domain validity and exact
root tag normality.

For a primitive function input x, the valid domain record of either
complete output witness makes its distinct input support an ordinarily
irreducible seed. Its ambient U-closure hull therefore belongs to
K(H) by (4b). Tag normality and U-closedness force the ENTIRE output
vertex set of EVERY witness for that input into this one hull.

Within the SAME canonical H-structure on that hull, uniqueness of
genuine Option(Set) values equates the two witnesses. All maps are
literal inclusion or full same-carrier canonical identification.
No counted weak vertex set or induction rank is enlarged: the hull
is solely an auxiliary coherence comparison.

Positive primitive function arity remains explicit: the nullary
positive-output case uses a different root-free closure argument.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- The complete OLD value vertex set for a fixed primitive function
input is UNIQUE in ANY U-closed candidate satisfying corrected (4b).
This proves the remaining value-coherence premise of the previous
ambient-to-original-function local-completion transfer, without fixed
canonical B-copy coverage or any new class axiom. -/
theorem genuineTagged2019_correctedCovered_uniqueCompleteValues
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity) :
    HasUniqueWholeMaskValues (wholeMaskTagReduct C) := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let Old := wholeMaskTagReduct C
  have hValid : HasValidCompleteMaskDomains Old :=
    genuineTagged2019_correctedCovered_validCompleteMaskDomains
      H C hClosed hCovered
  have hNormal : WholeMaskTagNormal C :=
    genuineTagged2019_correctedCovered_tagNormal
      H C hClosed hCovered
  intro F x U T hU hT
  obtain ⟨m, r, hr, q, t, hOld, hArgs, hSet⟩ := hU
  let pat : Language.FunctionInputPattern (L.withParts Parts) :=
    ⟨F, m, r, hr⟩
  let root : Fin m → V :=
    fun i => t (Fin.castAdd q.size i)
  have hRange : Set.range root = Set.range x :=
    equalityPattern_range_eq x r hr root hArgs
  let S : Set V := Set.range x
  let Hull : Set V := UClosureHull rules C S
  have hDom : Old.rel (.inr (.inl (pat,q))) root :=
    (hValid pat q t hOld).2
  have hRootIrred : (C.induce (Set.range root)).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (pat,q)))) root hDom
  have hSeedIrred : (C.induce S).Irreducible := by
    change (C.induce (Set.range x)).Irreducible
    rw [← hRange]
    exact hRootIrred
  have hHullClosed : IsUClosed rules (C.induce Hull) :=
    hClosed.induce_UClosureHull S
  have hHullIrred : IsUIrreducible rules (C.induce Hull) :=
    hClosed.irreducibleSeed_hull_isUIrreducible S hSeedIrred
  have hHullK : canonicalGenuineTagged2019Class H (C.induce Hull) :=
    hCovered Hull hHullClosed hHullIrred
  obtain ⟨hHullFinite, Target, partTarget, _, hTrans, hCanonical⟩ := hHullK
  letI : Finite Hull := hHullFinite
  have hTransPlus : FibreTransversal (Target.withParts partTarget)
      partTarget :=
    (Target.withParts_fibreTransversal_iff partTarget).mpr hTrans
  have hUniqueHull :
      HasUniqueWholeMaskValues (wholeMaskTagReduct (C.induce Hull)) := by
    rw [hCanonical]
    exact (Target.withParts partTarget).wholeMaskPatternGraph_hasUniqueValues
      partTarget hTransPlus
  have hxHull (i : Fin ((L.withParts Parts).funcArity F)) :
      x i ∈ Hull :=
    subset_UClosureHull rules C S ⟨i, rfl⟩
  let xHull : Fin ((L.withParts Parts).funcArity F) → Hull :=
    fun i => ⟨x i, hxHull i⟩

  have localize (Q : Set V) (hQ : HasWholeMaskValue Old F x Q) :
      ∃ QHull : Set Hull,
        HasWholeMaskValue (wholeMaskTagReduct (C.induce Hull))
          F xHull QHull ∧
        Q = Subtype.val '' QHull := by
    rcases hQ with
      ⟨k, s, hs, mask, tuple, hTuple, hInput, hOutput⟩
    let pattern : Language.FunctionInputPattern (L.withParts Parts) :=
      ⟨F, k, s, hs⟩
    let inputRoot : Fin k → V :=
      fun i => tuple (Fin.castAdd mask.size i)
    have hInputRange : Set.range inputRoot = S :=
      equalityPattern_range_eq x s hs inputRoot hInput
    have hRootHull : ∀ i : Fin k,
        tuple (Fin.castAdd mask.size i) ∈ Hull := by
      intro i
      apply subset_UClosureHull rules C S
      rw [← hInputRange]
      exact ⟨i, rfl⟩
    have hOutputHull : ∀ j : Fin mask.size,
        tuple (Fin.natAdd k j) ∈ Hull := by
      intro j
      have hMem := hNormal.completeOutput_mem_inputHull
        C hValid (hPos.withParts) pattern mask tuple hTuple j
      change tuple (Fin.natAdd k j) ∈
        UClosureHull rules C (Set.range inputRoot) at hMem
      rw [hInputRange] at hMem
      exact hMem
    have hAllHull : ∀ i : Fin (k + mask.size), tuple i ∈ Hull :=
      fun i => Fin.addCases hRootHull hOutputHull i
    let tupleHull : Fin (k + mask.size) → Hull :=
      fun i => ⟨tuple i, hAllHull i⟩
    let QHull : Set Hull :=
      Set.range (fun j : Fin mask.size => tupleHull (Fin.natAdd k j))
    have hValueHull :
        HasWholeMaskValue (wholeMaskTagReduct (C.induce Hull))
          F xHull QHull := by
      refine ⟨k, s, hs, mask, tupleHull, hTuple, ?_, rfl⟩
      intro i
      apply Subtype.ext
      exact hInput i
    have hQImage : Q = Subtype.val '' QHull := by
      rw [hOutput]
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨tupleHull (Fin.natAdd k j), ⟨j, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨j, hj⟩, hy⟩
        refine ⟨j, ?_⟩
        change a.1 = _ at hy
        exact hj ▸ hy
    exact ⟨QHull, hValueHull, hQImage⟩

  obtain ⟨UH, hUH, hUImage⟩ :=
    localize U ⟨m, r, hr, q, t, hOld, hArgs, hSet⟩
  obtain ⟨TH, hTH, hTImage⟩ := localize T hT
  have hEq : UH = TH := hUniqueHull F xHull UH TH hUH hTH
  calc
    U = Subtype.val '' UH := hUImage
    _ = Subtype.val '' TH := congrArg (fun Q : Set Hull => Subtype.val '' Q) hEq
    _ = T := hTImage.symm

end AllThoseRamseyClasses.Published
