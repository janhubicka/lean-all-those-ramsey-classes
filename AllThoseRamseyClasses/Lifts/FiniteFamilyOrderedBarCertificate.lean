import AllThoseRamseyClasses.Lifts.FiniteFamilyOrderedMaximalBar

/-!
# Track E: canonical ordered bar plus exact maximality/profile certificates

The certified ordered enlarged-witness theorem selects an honest
finite maximal induced-trace member Bbar and a full ORDERED marked
copy B -> Bbar. For the certified marked-copy Ramsey endgame we
also need the *same chosen* native maximizing witness W and the
proof that B's expanded component predicates are exactly the
canonical folded profile of W along the marked root.

This module keeps all the certificates together, with no extra
hypothesis. The finite native witness W is forbidden-free; its
shadow is literally Bbar's native shadow, and the full native
embedding iW agrees pointwise with the ordered mark. The root
profile is maximal among finite forbidden-free full native
extensions, so both positive and negative new tag predicates
are protected. The original complete set-valued function
fibres are preserved via a FULL native embedding.

This removes an otherwise easy-to-overlook existential mismatch:
one must not apply an endgame to an ordered Bbar chosen from W1
and a maximality proof supplied by an unrelated W2. The chosen
witness and all its certificates are produced together.

No sparse Ramsey control or local completion is constructed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An actual ordered enlarged age member Bbar constructed
together with the native witness W of B, its exact full
maximal-profile certificate, full forbidden avoidance,
and a full ORDERED marked B embedding agreeing with iW.

The theorem is unconditional for every finite maximal-trace
age member B. The order on Bbar is chosen so that the
prescribed order of B is respected on its marked copy. -/
theorem finiteNamedTrace_exists_orderedBarWithProfile
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB : Type} [LinearOrder VB]
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (hB : IsFiniteNamedMaximalTrace Family B) :
    ∃ (VW : Type) (_ : Finite VW)
      (W : Structure L VW)
      (Bbar : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VW)
      (o : LinearOrder VW),
      AvoidsFiniteNamedEHN Family W ∧
      IsFiniteNamedMaximalTrace Family Bbar ∧
      FiniteNamedTraceShadow Family Bbar = W ∧
      ∃ (iW : Structure.Embedding
          (FiniteNamedTraceShadow Family B) W),
        FiniteNamedCanonicalMaximalAlong Family
          (fun {U : Type} (E : Structure L U) =>
            FiniteNamedFiniteForbiddenFree Family E) iW ∧
        (∀ (tag : Family.ComponentTag)
          (xs : Fin (tag.width Family) → VB),
          B.rel (.inr tag) xs ↔
            (finiteNamedClosedComponentFoldedLift Family W).rel
              (.inr tag) (iW ∘ xs)) ∧
        ∃ (mark : Structure.Embedding B.withLinearOrder
            (@Structure.withLinearOrder _ VW Bbar o.toLT)),
          ∀ x : VB, mark x = iW x := by
  classical
  obtain ⟨hFinB, VW, W, hFinW, hAvoidW, iW,
    hMax, hRel⟩ := hB
  letI : Finite VW := hFinW
  obtain ⟨Bbar, hBar, hShadow, mark, hMark⟩ :=
    finiteNamed_exists_maximalBar_fromWitness
      Family B W hAvoidW iW hMax hRel
  obtain ⟨o, hOrder⟩ :=
    exists_finiteLinearOrder_extending_injection
      iW iW.injective
  letI : LinearOrder VW := o
  have hMono : StrictMono mark := by
    intro x y hxy
    rw [hMark x, hMark y]
    exact hOrder x y hxy
  let markOrdered : Structure.Embedding B.withLinearOrder
      (@Structure.withLinearOrder _ VW Bbar o.toLT) := {
    toFun := mark
    injective := mark.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R =>
          exact mark.map_rel_iff R xs
      | inr _ =>
          exact hMono.lt_iff_lt
    map_func := mark.map_func
  }
  exact ⟨VW, hFinW, W, Bbar, o,
    hAvoidW, hBar, hShadow,
    iW, hMax, hRel, markOrdered, hMark⟩

end AllThoseRamseyClasses.Lifts
