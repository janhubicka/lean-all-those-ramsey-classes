import AllThoseRamseyClasses.Lifts.FunctionalMarkedCopywiseRamseyTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalFiniteRestriction
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# Track E: a one-shot marked-witness Ramsey transfer from native avoidance

This is the actual second half of the alternative finite-family
Ramsey-lift argument, faithfully matching the mechanism described
after the partite construction in the 2019 paper.

Let B* be a finite maximal induced trace, with a chosen maximizing
native witness W_B. Let Bbar be an enlarged expanded structure
containing a designated FULL ORDERED copy of B*, and suppose Bbar's
native shadow contains a FULL copy of W_B extending that mark.

Given a finite expanded Ramsey control C with
  C -> (Bbar)^(A*)_k
and PROVIDED ITS NATIVE SHADOW AVOIDS THE NAMED FORBIDDEN FAMILY,
maximize the native shadow D of C along its whole carrier in a
single finite allowed extension M. The induced canonical trace
T of M on D is a genuine finite member of the maximal-trace age.

For every Bbar-copy t in C, the full shadow of t carries a
FULL W_B-copy into D. By maximality of W_B on the marked B*-root,
the marked B* is carried to a FULL expanded B*-copy in T. Both
old function fibre equality and negative tag reflection are
preserved, not just positive homomorphism preservation. The vertex
map C -> T is literally the identity on the native shadow and
preserves the external order.

The generic marked-copy Ramsey transfer now proves T -> (B*)^(A*)_k.
No preservation of unrelated B*-copies in C is required.

The remaining E2 obligation is to construct an ambient Ramsey control
with EXACT weak small-test completions; the separate weak-local
avoidance lemma then discharges the native avoidance hypothesis.
This theorem does NOT prove that such a sparse control exists, and
it is NOT a proof of the printed unrestricted regular-family lift.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- The final finite ordered Ramsey arrow after a sparse picture
has become NATIVE forbidden-free. Bbar's native W_B witness is
required to extend its marked B*-copy, but the target need not
preserve any other B*-copy of the original control.

In particular, neither the added component tags nor the native
function fibres are assumed to reflect under the arbitrary
control-to-completion map: reflection is DERIVED from the
full native witness embeddings and maximality. -/
theorem finiteNamedMarkedWitnessRamsey_of_nativeAvoidance
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VB VP VC VW : Type}
    [LinearOrder VA] [LinearOrder VB]
    [LinearOrder VP] [LinearOrder VC]
    [Finite VC]
    (A : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VA)
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (Bbar : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VP)
    (C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC)
    (W : Structure L VW)
    (iW : Structure.Embedding (FiniteNamedTraceShadow Family B) W)
    (hMax : FiniteNamedCanonicalMaximalAlong Family
      (fun {U : Type} (E : Structure L U) =>
        FiniteNamedFiniteForbiddenFree Family E) iW)
    (hRel : ∀ (tag : Family.ComponentTag)
        (xs : Fin (tag.width Family) → VB),
        B.rel (.inr tag) xs ↔
          (finiteNamedClosedComponentFoldedLift Family W).rel
            (.inr tag) (iW ∘ xs))
    (mark : Structure.Embedding B.withLinearOrder Bbar.withLinearOrder)
    (wBar : Structure.Embedding W (FiniteNamedTraceShadow Family Bbar))
    (hMark : ∀ x : VB, wBar (iW x) = mark x)
    {κ : Type v} [Nonempty κ]
    (hArrow : Structure.Arrow A.withLinearOrder Bbar.withLinearOrder
      C.withLinearOrder κ)
    (hAvoid : AvoidsFiniteNamedEHN Family (FiniteNamedTraceShadow Family C)) :
    ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      Structure.Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder _ VT T o.toLT) κ := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  let D : Structure L VC := FiniteNamedTraceShadow Family C
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨VM, M, hFinM, hAvoidM, eDM, hMaxD⟩ :=
    finiteNamed_exists_finite_maximal_extension Family dId hAvoid
  letI : Finite VM := hFinM
  let rootD : Structure.Embedding D M := eDM.comp dId
  let T := finiteNamedCanonicalTrace Family rootD
  have hT : IsFiniteNamedMaximalTrace Family T :=
    finiteNamedCanonicalTrace_mem_age Family rootD hAvoidM hMaxD
  have hCopied :
      ∀ t : Structure.Embedding Bbar.withLinearOrder
          C.withLinearOrder,
        ∃ bT : Structure.Embedding B.withLinearOrder
            (@Structure.withLinearOrder _ VC T
              (inferInstance : LinearOrder VC).toLT),
          ∀ x : VB, bT x = t (mark x) := by
    intro t
    let tShadow : Structure.Embedding
        (FiniteNamedTraceShadow Family Bbar) D :=
      functionalShadowBigEmbedding L Family.ComponentTag
        (fun tag => tag.width Family) t.linearOrderReduct
    let k : Structure.Embedding W D := tShadow.comp wBar
    let base : Structure.Embedding (FiniteNamedTraceShadow Family B) D :=
      k.comp iW
    let j : Structure.Embedding B T :=
      finiteNamedMaximalTrace_embedding_into_allowed_trace
        Family B W iW hMax hRel
        D base M ⟨hFinM, hAvoidM⟩
        rootD (eDM.comp k) (by intro x; rfl)
    have hj (x : VB) : j x = t (mark x) := by
      change k (iW x) = t (mark x)
      change t (wBar (iW x)) = t (mark x)
      exact congrArg t (hMark x)
    have hjMono : StrictMono j := by
      intro x y hxy
      rw [hj x, hj y]
      exact t.strictMono (mark.strictMono hxy)
    let jo : Structure.Embedding B.withLinearOrder
        (@Structure.withLinearOrder _ VC T
          (inferInstance : LinearOrder VC).toLT) := {
      toFun := j
      injective := j.injective
      map_rel_iff := by
        intro R xs
        cases R with
        | inl R => exact j.map_rel_iff R xs
        | inr _ => exact hjMono.lt_iff_lt
      map_func := j.map_func
    }
    exact ⟨jo, hj⟩
  have hFinal : Structure.Arrow A.withLinearOrder B.withLinearOrder
      (@Structure.withLinearOrder _ VC T
        (inferInstance : LinearOrder VC).toLT) κ :=
    functionalArrow_of_markedBCopywiseCompletion
      (f := fun x : VC => x) mark hArrow hCopied
  exact ⟨VC, inferInstance, inferInstance, T, hT, hFinal⟩

end AllThoseRamseyClasses.Lifts
