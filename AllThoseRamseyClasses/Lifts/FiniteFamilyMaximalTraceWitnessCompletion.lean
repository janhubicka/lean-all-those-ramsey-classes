import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceRamseyTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalFiniteRestriction
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# Track E: lift a common native witness diagram to a full copywise completion

For the alternative finite-named, all-closed-component FOLDED lift,
the critical distinction is between existence of a native forbidden-free
completion of a sparse Ramsey control and reflection of the added tags.

Suppose B* has a genuine finite forbidden-free maximizing witness W_B.
For each B*-copy in a control C, suppose one FULL copy of W_B has been
embedded into the SAME finite native forbidden-free D, over a single
prescribed vertex map f : C -> D. These embeddings may have different
images away from B*, but on B* they MUST all agree with f.

We MAXIMIZE the canonical component profile along the entire finite
root D in one finite forbidden-free extension M. The induced canonical
trace of M on D is a genuine age member. Each W_B -> D -> M is an
allowed extension, so maximality of W_B on its displayed B* root
implies EXACT positive and negative folded-tag reflection on B*.
Old relation and COMPLETE set-valued function-fibre reflection comes
from the original FULL embeddings. Thus f preserves every B*-copy
as a genuine expanded full embedding.

The same mechanism works with an external order if each specified
root copy is strictly ordered by f. No full embedding of the whole
control C is assumed.

This proves the E3 reflection/assembly step from explicitly supplied
common native witness embeddings. It does NOT construct those embeddings,
does NOT prove the local sparsening needed for E2, and does NOT prove
the full finite-family Ramsey class theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Reuse the existing maximal trace transport directly when one
maximizing witness W_B embeds into a common native root D, which
itself embeds into an allowed finite maximal extension M.

The produced embedding reflects ALL new folded tags, including
colliding root coordinates, and every old function output fibre.
Its underlying vertex map is the composite W_B-root inclusion. -/
noncomputable def finiteNamedTraceEmbedding_of_commonWitness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW VD VM : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
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
    (D : Structure L VD)
    (M : Structure L VM)
    (hM : FiniteNamedFiniteForbiddenFree Family M)
    (eDM : Structure.Embedding D M)
    (k : Structure.Embedding W D) :
    Structure.Embedding B (finiteNamedCanonicalTrace Family eDM) :=
  finiteNamedMaximalTrace_embedding_into_allowed_trace
    Family B W iW hMax hRel
    D (k.comp iW) M hM eDM (eDM.comp k)
    (by intro x; rfl)

/-- E3 without external orders: a common finite forbidden-free
native completion D containing a FULL copy of the selected B*
maximizing witness over EVERY B*-copy of C is enough to produce
an ACTUAL finite maximal-trace copywise completion.

This is a genuinely native diagram condition: no reflection of
added predicates in the target is postulated. -/
theorem finiteNamedTraceCopywiseCompletion_of_commonWitness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW VC VD : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
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
    (D : Structure L VD)
    (hFinD : Finite VD)
    (hAvoidD : AvoidsFiniteNamedEHN Family D)
    (f : VC → VD)
    (hCopies : ∀ b : Structure.Embedding B C,
      ∃ (k : Structure.Embedding W D),
        ∀ x : VB, k (iW x) = f (b x)) :
    FiniteNamedTraceCopywiseCompletion Family B C := by
  classical
  letI : Finite VD := hFinD
  letI : Fintype VD := Fintype.ofFinite VD
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨VM, M, hFinM, hAvoidM, eDM, hMaxD⟩ :=
    finiteNamed_exists_finite_maximal_extension Family dId hAvoidD
  letI : Finite VM := hFinM
  let rootD : Structure.Embedding D M := eDM.comp dId
  have hMember :
      IsFiniteNamedMaximalTrace Family
        (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedCanonicalTrace_mem_age Family rootD hAvoidM hMaxD
  refine ⟨VD, finiteNamedCanonicalTrace Family rootD,
    hMember, f, ?_⟩
  intro b
  obtain ⟨k, hk⟩ := hCopies b
  let j : Structure.Embedding B
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedTraceEmbedding_of_commonWitness
      Family B W iW hMax hRel D M
      ⟨hFinM, hAvoidM⟩ rootD k
  exact ⟨j, by intro x; exact hk x⟩

/-- Ordered E3: the same native common-witness completion becomes a
full ordered B*-copywise completion if the prescribed common vertex
map respects the order on EACH B*-copy.

There is no requirement for f to be injective or order-preserving
globally on the whole ambient control C; only selected B*-copies
are protected. -/
theorem finiteNamedOrderedTraceCopywiseCompletion_of_commonWitness
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VW VC VD : Type} [LinearOrder VB] [LinearOrder VC]
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
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
    (D : Structure L VD)
    (hFinD : Finite VD)
    (hAvoidD : AvoidsFiniteNamedEHN Family D)
    (o : LinearOrder VD)
    (f : VC → VD)
    (hCopies : ∀ b : Structure.Embedding
        B.withLinearOrder C.withLinearOrder,
      ∃ (k : Structure.Embedding W D),
        (∀ x : VB, k (iW x) = f (b x)) ∧
        (∀ x y : VB, x < y →
          @LT.lt VD o.toLT (f (b x)) (f (b y)))) :
    FiniteNamedOrderedTraceCopywiseCompletion Family B C := by
  classical
  letI : Finite VD := hFinD
  letI : LinearOrder VD := o
  letI : Fintype VD := Fintype.ofFinite VD
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨VM, M, hFinM, hAvoidM, eDM, hMaxD⟩ :=
    finiteNamed_exists_finite_maximal_extension Family dId hAvoidD
  letI : Finite VM := hFinM
  let rootD : Structure.Embedding D M := eDM.comp dId
  have hMember :
      IsFiniteNamedMaximalTrace Family
        (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedCanonicalTrace_mem_age Family rootD hAvoidM hMaxD
  refine ⟨VD, o, finiteNamedCanonicalTrace Family rootD,
    hMember, f, ?_⟩
  intro b
  obtain ⟨k, hk, hOrder⟩ := hCopies b
  let j : Structure.Embedding B
      (finiteNamedCanonicalTrace Family rootD) :=
    finiteNamedTraceEmbedding_of_commonWitness
      Family B W iW hMax hRel D M
      ⟨hFinM, hAvoidM⟩ rootD k
  have hjMono : StrictMono j := by
    intro x y hxy
    change k (iW x) < k (iW y)
    rw [hk x, hk y]
    exact hOrder x y hxy
  let jo : Structure.Embedding B.withLinearOrder
      (@Structure.withLinearOrder _ VD
        (finiteNamedCanonicalTrace Family rootD) o.toLT) := {
    toFun := j
    injective := j.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R =>
          exact j.map_rel_iff R xs
      | inr _ =>
          exact hjMono.lt_iff_lt
    map_func := j.map_func
  }
  exact ⟨jo, by intro x; exact hk x⟩

end AllThoseRamseyClasses.Lifts
