import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceTransfer

/-!
# Joint embedding transfer to the hereditary regular global-lift age

The original regular global canonical lift produces finite maximal
induced traces over every finite K-allowed native structure. If
the finite native class K itself has FULL joint embedding, then
so does the hereditary age of maximal traces.

This follows by embedding two native maximizing witnesses in a
common finite native allowed witness D, choosing a further finite
allowed extension maximal along D, and transporting BOTH original
expanded traces into the induced trace on D.

This result is properly CONDITIONAL: neither strong AP nor
JEP follows automatically from regularity, and disconnected
forbidden families may prevent native JEP. All old native
function-value fibres are preserved exactly. No conclusion of
the printed Section 3 unrestricted strong amalgamation or Ramsey
theorem is claimed here.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Full JEP of the FINITE native K-allowed functional structures.
The two embeddings are FULL, preserving each original function
value set exactly, rather than merely positive incidences. -/
def GlobalNativeFiniteJEP
    (K : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {UA UB : Type}
    (A : Structure L UA) (B : Structure L UB),
    Finite UA → Finite UB →
    K A → K B →
    ∃ (UC : Type) (C : Structure L UC),
      Finite UC ∧ K C ∧
      ∃ (_eA : Structure.Embedding A C)
        (_eB : Structure.Embedding B C), True

/-- For an arbitrary regular forbidden-piece family, native full
finite JEP transfers to the genuine finite hereditary maximal
induced global canonical-trace age. No AP or Ramsey assumption;
the required native joint embedding is explicit. -/
theorem globalFiniteMaximalTraceAge_JEP_of_nativeJEP
    (F K : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hJEP : GlobalNativeFiniteJEP K)
    {VY VZ : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F K Y)
    (hZ : IsGlobalFiniteMaximalTrace F K Z) :
    ∃ (VT : Type)
      (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F K T ∧
      ∃ (_jY : Structure.Embedding Y T)
        (_jZ : Structure.Embedding Z T), True := by
  classical
  obtain ⟨_hFinY, UWY, WY, hFinWY, hKWY,
    iY, hMaxY, hRelY⟩ := hY
  obtain ⟨_hFinZ, UWZ, WZ, hFinWZ, hKWZ,
    iZ, hMaxZ, hRelZ⟩ := hZ
  obtain ⟨VD, D, hFinD, hKD, eWY, eWZ, _⟩ :=
    hJEP WY WZ hFinWY hFinWZ hKWY hKWZ
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
    eWY.comp iY
  let baseZ : Structure.Embedding
      (functionalShadowBig L
        (GlobalFunctionalPieceSymbol F)
        (globalFunctionalPieceArity F) Z) D :=
    eWZ.comp iZ
  let jY : Structure.Embedding Y
      (globalCanonicalInducedTrace F rootD) :=
    globalMaximalTrace_embedding_into_allowed_trace
      F K Y WY iY hMaxY hRelY D baseY M
      hKM rootD (eDM.comp eWY)
      (by intro y; rfl)
  let jZ : Structure.Embedding Z
      (globalCanonicalInducedTrace F rootD) :=
    globalMaximalTrace_embedding_into_allowed_trace
      F K Z WZ iZ hMaxZ hRelZ D baseZ M
      hKM rootD (eDM.comp eWZ)
      (by intro z; rfl)
  exact ⟨VD, globalCanonicalInducedTrace F rootD,
    hMember, jY, jZ, True.intro⟩

end AllThoseRamseyClasses.Lifts
