import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceTransfer
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Reduction of original Section 3 strong AP to shadow avoidance

The finite maximal induced-trace age of the ORIGINAL global
root-injective canonical lift has hereditary membership, regularity-
based finite witnesses, and complete full trace transfer. What
remains for strong amalgamation is a genuinely combinatorial fact:

Whenever two K-allowed native witnesses induce the same full
GLOBAL canonical piece-class relations on a common full root,
their genuine native functional free amalgam is still K-allowed.

We give that fact an EXPLICIT class hypothesis. The present theorem
constructs the whole finite strong amalgam of maximal global traces
from it: the allowed native free amalgam, a finite allowed maximal
extension, the FULL induced global trace, and the two full expanded
embeddings with precisely their prescribed intersection.

This isolates the exact unresolved 2019 forbidden-witness flip /
noninjective-root and multicomponent issue; it is NOT a proof of
the missing shadow-avoidance hypothesis or of the unrestricted
Section 3 theorem. It makes no use of an invalid image quotient
being a full embedding, and retains all original function values.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The precise still-unverified global-piece shadow amalgamation
principle needed to complete the printed Section 3 strong-AP
proof. It is a mathematical hypothesis, not a theorem here.

The native witnesses must each lie in K, agree on ALL new global
piece-class relations over the FULL common old root, and the target
must be a genuine FULL functional free amalgam. The conclusion is
that the old target remains in K. -/
def GlobalCanonicalShadowFreeAmalgamation
    (F K : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {UX UA UB UT : Type}
    (X : Structure L UX)
    (A : Structure L UA) (B : Structure L UB)
    (D : Structure L UT)
    (iA : Structure.Embedding X A)
    (iB : Structure.Embedding X B)
    (jA : Structure.Embedding A D)
    (jB : Structure.Embedding B D),
    Structure.IsFreeAmalgam iA iB jA jB →
    GlobalCanonicalLiftsAgreeOn F iA iB →
    K A → K B → K D

/-- Strong amalgamation of the ACTUAL hereditary maximal induced
global-trace age follows from the ONE isolated native-shadow
avoidance lemma. This theorem gives a real finite lifted
structure, two FULL embeddings, and EXACT intersection.

No Ramsey or free amalgamation in the NEW relation language is
claimed. The printed 2019 theorem still needs an unconditional
proof of GlobalCanonicalShadowFreeAmalgamation. -/
theorem globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hFreeK : GlobalCanonicalShadowFreeAmalgamation F K)
    {VX VY VZ : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F K Y)
    (hZ : IsGlobalFiniteMaximalTrace F K Z)
    (fY : Structure.Embedding X Y)
    (fZ : Structure.Embedding X Z) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F K T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T),
        ∀ y : VY, ∀ z : VZ,
          jY y = jZ z ↔
            ∃ x : VX, y = fY x ∧ z = fZ x := by
  classical
  obtain ⟨hFinY, UWY, WY, hFinWY, hKWY,
    iY, hMaxY, hRelY⟩ := hY
  obtain ⟨hFinZ, UWZ, WZ, hFinWZ, hKWZ,
    iZ, hMaxZ, hRelZ⟩ := hZ
  letI : Finite VY := hFinY
  letI : Finite VZ := hFinZ
  letI : Finite UWY := hFinWY
  letI : Finite UWZ := hFinWZ
  have hFinX : Finite VX := Finite.of_injective fY fY.injective
  letI : Finite VX := hFinX
  let Root : Structure L VX :=
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) X
  let sY : Structure.Embedding Root
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y) :=
    functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) fY
  let sZ : Structure.Embedding Root
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Z) :=
    functionalShadowBigEmbedding L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F) fZ
  let pY : Structure.Embedding Root WY := iY.comp sY
  let pZ : Structure.Embedding Root WZ := iZ.comp sZ
  have hAgree : GlobalCanonicalLiftsAgreeOn F pY pZ := by
    intro s xs
    have hEY := fY.map_rel_iff (.inr s) xs
    have hEZ := fZ.map_rel_iff (.inr s) xs
    change Y.rel (.inr s) (sY ∘ xs) ↔
      X.rel (.inr s) xs at hEY
    change Z.rel (.inr s) (sZ ∘ xs) ↔
      X.rel (.inr s) xs at hEZ
    change
      (globalFunctionalCanonicalLift F WY).rel
        (.inr s) (iY ∘ sY ∘ xs) ↔
      (globalFunctionalCanonicalLift F WZ).rel
        (.inr s) (iZ ∘ sZ ∘ xs)
    calc
      _ ↔ Y.rel (.inr s) (sY ∘ xs) :=
        (hRelY s (sY ∘ xs)).symm
      _ ↔ X.rel (.inr s) xs := hEY
      _ ↔ Z.rel (.inr s) (sZ ∘ xs) := hEZ.symm
      _ ↔ _ := hRelZ s (sZ ∘ xs)
  let VD := Structure.FreeAmalgam.Vertex Root WY WZ pY pZ
  let D : Structure L VD :=
    Structure.FreeAmalgam.amalgam Root WY WZ pY pZ
  let jWY : Structure.Embedding WY D :=
    Structure.FreeAmalgam.leftEmbedding Root WY WZ pY pZ
  let jWZ : Structure.Embedding WZ D :=
    Structure.FreeAmalgam.rightEmbedding Root WY WZ pY pZ
  have hFree : Structure.IsFreeAmalgam
      pY pZ jWY jWZ :=
    Structure.FreeAmalgam.isFreeAmalgam Root WY WZ pY pZ
  have hKD : K D :=
    hFreeK Root WY WZ D pY pZ jWY jWZ
      hFree hAgree hKWY hKWZ
  have hFinD : Finite VD := by
    let incl : UWY ⊕ UWZ → VD :=
      fun v => match v with
      | .inl y => jWY y
      | .inr z => jWZ z
    apply Finite.of_surjective incl
    intro x
    rcases hFree.covers x with ⟨y, hy⟩ | ⟨z, hz⟩
    · exact ⟨Sum.inl y, hy.symm⟩
    · exact ⟨Sum.inr z, hz.symm⟩
  letI : Finite VD := hFinD
  letI : Fintype VD := Fintype.ofFinite VD
  let dId : Structure.Embedding D D := Structure.Embedding.id D
  obtain ⟨UM, M, hKM, eDM, hMaxD⟩ :=
    regularGlobal_exists_maximal_extension
      F (FiniteGlobalAllowed K) hRegular
      dId ⟨hKD, hFinD⟩
  letI : Finite UM := hKM.2
  let rootD : Structure.Embedding D M := eDM.comp dId
  have hMember :
      IsGlobalFiniteMaximalTrace F K
        (globalCanonicalInducedTrace F rootD) :=
    globalCanonicalInducedTrace_mem_maximalAge
      F K rootD hKM.1 hMaxD
  let baseY : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Y) D :=
    jWY.comp iY
  let baseZ : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Z) D :=
    jWZ.comp iZ
  let jY : Structure.Embedding Y
      (globalCanonicalInducedTrace F rootD) :=
    globalMaximalTrace_embedding_into_allowed_trace
      F K Y WY iY hMaxY hRelY D baseY M
      hKM rootD (eDM.comp jWY)
      (by intro y; rfl)
  let jZ : Structure.Embedding Z
      (globalCanonicalInducedTrace F rootD) :=
    globalMaximalTrace_embedding_into_allowed_trace
      F K Z WZ iZ hMaxZ hRelZ D baseZ M
      hKM rootD (eDM.comp jWZ)
      (by intro z; rfl)
  refine ⟨VD, globalCanonicalInducedTrace F rootD,
    hMember, jY, jZ, ?_⟩
  intro y z
  change jWY (iY y) = jWZ (iZ z) ↔
      ∃ x : VX, y = fY x ∧ z = fZ x
  constructor
  · intro h
    obtain ⟨x, hy, hz⟩ :=
      (hFree.overlap (iY y) (iZ z)).mp h
    exact ⟨x, iY.injective hy, iZ.injective hz⟩
  · rintro ⟨x, rfl, rfl⟩
    exact (hFree.overlap (iY (fY x)) (iZ (fZ x))).mpr
      ⟨x, rfl, rfl⟩

end AllThoseRamseyClasses.Lifts
