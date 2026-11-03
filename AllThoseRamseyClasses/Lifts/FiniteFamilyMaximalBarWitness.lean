import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalFiniteRestriction

/-!
# Track E: choose the enlarged marked witness INSIDE the lifted age

The final finite-family Ramsey proof uses a larger witness Bbar
carrying one distinguished full B-copy. A mere canonical lift
of the original native witness W_B is not automatically in the
hereditary maximal-trace age: it may not be maximal on all of W_B.

There is a genuine finite age member Bbar with carrier W_B:
choose a finite allowed extension M of W_B whose complete folded
tag profile is maximal on the ENTIRE W_B root. Take the induced
canonical trace of M on W_B. This belongs to the maximal-trace
age by definition, and its old functional shadow is exactly W_B.

The original B-trace remains a full expanded substructure of
Bbar. Indeed W_B was already maximizing along the displayed
B root, and the allowed extension W_B -> M cannot add any
folded tags on that root. Old relations and ENTIRE original
set-valued function fibres are reflected by the native full
embedding. No global free amalgamation of the new tag language,
or extension of arbitrary weak embeddings, is assumed.

Thus Bbar can be chosen in the SAME hereditary strong AP class
as B. This is the natural marked input for the still missing
E2 partite/sparse completion. External linear orders are
provided separately by the finite-witness order-extension lemma.
The unrestricted regular infinite-family Section 3 theorem is
not claimed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- From one actual finite forbidden-free maximizing witness W
of an expanded trace B, construct a FINITE maximal-trace age
member Bbar on exactly the native carrier W, together with
a FULL expanded marked B-copy extending its original shadow
embedding iW.

In particular Bbar itself is available for strong amalgamation
in the age. This does not assert any Ramsey property of Bbar. -/
theorem finiteNamed_exists_maximalBar_fromWitness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW : Type} [Finite VW]
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (W : Structure L VW)
    (hAvoid : AvoidsFiniteNamedEHN Family W)
    (iW : Structure.Embedding
      (FiniteNamedTraceShadow Family B) W)
    (hMax : FiniteNamedCanonicalMaximalAlong Family
      (fun {U : Type} (E : Structure L U) =>
        FiniteNamedFiniteForbiddenFree Family E) iW)
    (hRel : ∀ (tag : Family.ComponentTag)
      (xs : Fin (tag.width Family) → VB),
      B.rel (.inr tag) xs ↔
        (finiteNamedClosedComponentFoldedLift Family W).rel
          (.inr tag) (iW ∘ xs)) :
    ∃ (Bbar : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VW),
      IsFiniteNamedMaximalTrace Family Bbar ∧
      FiniteNamedTraceShadow Family Bbar = W ∧
      ∃ (mark : Structure.Embedding B Bbar),
        ∀ x : VB, mark x = iW x := by
  classical
  letI : Fintype VW := Fintype.ofFinite VW
  let wId : Structure.Embedding W W := Structure.Embedding.id W
  obtain ⟨VM, M, hFinM, hAvoidM, eWM, hMaxW⟩ :=
    finiteNamed_exists_finite_maximal_extension Family wId hAvoid
  letI : Finite VM := hFinM
  let rootW : Structure.Embedding W M := eWM.comp wId
  let Bbar := finiteNamedCanonicalTrace Family rootW
  have hBar : IsFiniteNamedMaximalTrace Family Bbar :=
    finiteNamedCanonicalTrace_mem_age Family rootW hAvoidM hMaxW
  have hShadow : FiniteNamedTraceShadow Family Bbar = W :=
    finiteNamedCanonicalTrace_shadow Family rootW
  let mark : Structure.Embedding B Bbar :=
    finiteNamedMaximalTrace_embedding_into_allowed_trace
      Family B W iW hMax hRel
      W iW M ⟨hFinM, hAvoidM⟩ rootW eWM
      (by intro x; rfl)
  exact ⟨Bbar, hBar, hShadow, mark, by intro x; rfl⟩

/-- Every actual finite maximal-trace age member B has a
finite native forbidden-free witness W and a LARGER member Bbar
of the SAME expanded age with literal old shadow W. The
original B is fully embedded into Bbar, and the marked vertex
map is the original full shadow-to-witness embedding.

No age JEP, native common-root existence or Ramsey hypothesis
is required for this canonical enlarged witness. -/
theorem finiteNamedMaximalTraceAge_exists_markedBar
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (hB : IsFiniteNamedMaximalTrace Family B) :
    ∃ (VW : Type) (W : Structure L VW),
      Finite VW ∧ AvoidsFiniteNamedEHN Family W ∧
      ∃ (iW : Structure.Embedding
        (FiniteNamedTraceShadow Family B) W)
        (Bbar : Structure
          (functionalLiftLanguageBig L Family.ComponentTag
            (fun tag => tag.width Family)) VW),
        IsFiniteNamedMaximalTrace Family Bbar ∧
        FiniteNamedTraceShadow Family Bbar = W ∧
        ∃ (mark : Structure.Embedding B Bbar),
          ∀ x : VB, mark x = iW x := by
  obtain ⟨_hFinB, VW, W, hFinW, hAvoidW,
    iW, hMax, hRel⟩ := hB
  letI : Finite VW := hFinW
  obtain ⟨Bbar, hBar, hShadow, mark, hmark⟩ :=
    finiteNamed_exists_maximalBar_fromWitness
      Family B W hAvoidW iW hMax hRel
  exact ⟨VW, W, hFinW, hAvoidW, iW,
    Bbar, hBar, hShadow, mark, hmark⟩

end AllThoseRamseyClasses.Lifts
