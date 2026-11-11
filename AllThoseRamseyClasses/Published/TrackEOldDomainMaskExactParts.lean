import AllThoseRamseyClasses.Published.TrackENativeFinalFibreTransversal
import PartiteConstruction.Functional.WholeMaskOldEmbeddingTransport2019
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns

/-!
# Track E2: source-defined OLD active-domain masks determine target output parts

The whole-mask encoding records the exact set of output parts on each
active input root, even if some (or all) of its output vertices lie outside
the original exact weak test S. This separate OLD domain relation persists
under induced restriction to S, unlike the whole-output graph relation.

Only a POSITIVE map on these domain-mask relations is required to preserve
the set of output parts of every nonempty source fibre on exactly S and
f. This uses input equality-pattern factorization and the already verified
canonical-domain existence lemma, so repeated inputs and nullaries are
included. It does NOT imply positive output-incidence preservation, full
ambient irreducible protection or an E2 sparse Ramsey constructor.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A positive OLD active-output-part mask map on the same literal S and
f preserves the EXACT original output-part set of every NONEMPTY source
fibre. Neither the target full values nor any positive output-graph tuples
are assumed preserved. The source mask remains available even when the
whole function-value tuple is not contained in S. -/
theorem nativeOutputPartMask_eq_of_oldDomainMap
    {V W : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V)
    (B : FunctionalPartite.System L Parts W)
    (S : Set V) (f : S → W)
    (hDomain :
      ∀ (p : Language.FunctionInputPattern L)
        (q : Language.CompleteOutputParts Parts)
        (rootS : Fin p.rootSize → S),
        ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).rel
          (.inr (.inl (p, q))) rootS →
        (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part).rel
          (.inr (.inl (p, q))) (f ∘ rootS))
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S)
    (hNonempty : (A.func F (Subtype.val ∘ xs)).Nonempty) :
    B.part '' (B.func F (f ∘ xs)) =
      A.part '' (A.func F (Subtype.val ∘ xs)) := by
  classical
  let U : Set V := A.func F (Subtype.val ∘ xs)
  let T : Set W := B.func F (f ∘ xs)
  have hTransA : FibreTransversal A.toStructure.toNonemptyPartial A.part :=
    (nativeFunctionFibreTransversal_iff_partial
      A.toStructure A.part).mp A.funcTransversal
  have hSome : A.toStructure.toNonemptyPartial.func F
      (Subtype.val ∘ xs) = some U := by
    change (if U.Nonempty then some U else none) = some U
    exact if_pos hNonempty
  have hDefined : A.toStructure.toNonemptyPartial.Defined F
      (Subtype.val ∘ xs) := ⟨U, hSome⟩
  obtain ⟨m, r, hr, q, root, hSourceDom, hArgs⟩ :=
    (A.toStructure.toNonemptyPartial.hasWholeMaskDomain_iff_sourceDefined
      A.part hTransA F (Subtype.val ∘ xs)).mpr hDefined
  let pat : Language.FunctionInputPattern L := ⟨F, m, r, hr⟩
  have hRootS (i : Fin m) : root i ∈ S := by
    obtain ⟨j, hj⟩ := hr i
    have hx : (Subtype.val ∘ xs) j ∈ S := (xs j).2
    rw [hArgs j] at hx
    simpa only [hj] using hx
  let rootS : Fin m → S := fun i => ⟨root i, hRootS i⟩
  have hSourceDomS :
      ((A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part).induce S).rel
        (.inr (.inl (pat, q))) rootS := hSourceDom
  have hTargetDom := hDomain pat q rootS hSourceDomS
  change Function.Injective root ∧
    ∃ T0 : Set V,
      A.toStructure.toNonemptyPartial.func F (root ∘ r) = some T0 ∧
      A.part '' T0 = Set.range q.label at hSourceDom
  obtain ⟨_hInj, T0, hValueA, hPartsA⟩ := hSourceDom
  have hArgsA : root ∘ r = Subtype.val ∘ xs := by
    funext i
    exact (hArgs i).symm
  rw [hArgsA] at hValueA
  have hT0 : T0 = U := Option.some.inj (hValueA.symm.trans hSome)
  change Function.Injective (f ∘ rootS) ∧
    ∃ T1 : Set W,
      B.toStructure.toNonemptyPartial.func F ((f ∘ rootS) ∘ r) = some T1 ∧
      B.part '' T1 = Set.range q.label at hTargetDom
  obtain ⟨_hInjTarget, T1, hValueB, hPartsB⟩ := hTargetDom
  have hArgsB : (f ∘ rootS) ∘ r = f ∘ xs := by
    funext i
    apply congrArg f
    apply Subtype.ext
    exact (hArgs i).symm
  rw [hArgsB] at hValueB
  have hNonemptyTarget : T.Nonempty := by
    by_contra hn
    have hNone : B.toStructure.toNonemptyPartial.func F (f ∘ xs) = none := by
      change (if T.Nonempty then some T else none) = none
      simp [hn]
    rw [hNone] at hValueB
    cases hValueB
  have hT1 : T = T1 := by
    change (if T.Nonempty then some T else none) = some T1 at hValueB
    simpa only [if_pos hNonemptyTarget, Option.some.injEq] using hValueB
  change B.part '' T = A.part '' U
  rw [hT1, hPartsB, ← hT0]
  exact hPartsA.symm

end AllThoseRamseyClasses.Published
