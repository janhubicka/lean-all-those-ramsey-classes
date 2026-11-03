import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3ClassAssembly

/-!
# Track F: exact finite named-carrier maximal-trace age

For a FINITE original language (finite types of old relation and
function symbols) and a finite carrier V, there are finitely many
original native structures on V. This counts COMPLETE set-valued
partial-function fibres and positive/negative relation tuples,
including nullary ones.

For a globally regular forbidden-piece family, the exact fibre of
actual original ROOT-INJECTIVE maximal traces over EACH such native
structure is finite (already proved in
`GlobalMaximalTraceExactFibre.lean`). Encoding an actual maximal trace
by its entire native shadow and its genuine maximal-trace fibre
therefore proves FINITENESS of the total named-carrier age.

This is a prerequisite for the countability of isomorphism types of
the finite regular global lift over a finite native signature.
It is INDEPENDENT of the still open general shadow-avoidance,
strong amalgamation, Fraisse-limit existence, and Ramsey results.

No unbounded regular F is replaced by a finite family; no folded
root relations or non-full function embeddings are used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- A finite native signature has finitely many FULL relation/function
structures on each fixed finite carrier. Each set-valued function
fibre is one of finitely many subsets of that carrier; no totality
or positivity of function arities is assumed. -/
theorem finiteNativeStructures_onFiniteCarrier
    (L : Language.{u}) (V : Type)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] [Finite V] :
    Finite (Structure L V) := by
  classical
  let codes :
      Structure L V →
        ((R : L.RelSymbol) →
          (Fin (L.relArity R) → V) → Prop) ×
        ((f : L.FuncSymbol) →
          (Fin (L.funcArity f) → V) → Set V) :=
    fun A => (A.rel, A.func)
  have hCodes : Finite
      (((R : L.RelSymbol) →
          (Fin (L.relArity R) → V) → Prop) ×
        ((f : L.FuncSymbol) →
          (Fin (L.funcArity f) → V) → Set V)) := by
    infer_instance
  letI := hCodes
  apply Finite.of_injective codes
  intro A B h
  have hRel : A.rel = B.rel :=
    congrArg Prod.fst h
  have hFunc : A.func = B.func :=
    congrArg Prod.snd h
  cases A with
  | mk relA funcA =>
    cases B with
    | mk relB funcB =>
      change relA = relB at hRel
      change funcA = funcB at hFunc
      cases hRel
      cases hFunc
      rfl

/-- The ENTIRE actual original regular maximal-trace age over one
fixed finite labelled carrier is finite: a genuine trace is
determined by a finite original native table and one of the finite
actual maximal-trace options for that exact native table.

No strong amalgamation, JEP, Ramsey or Claim 2 assumption enters. -/
theorem globalMaximalTraceAge_finite_onFiniteCarrier
    (L : Language.{u})
    (F K : ∀ {W : Type}, Structure L W → Prop)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hRegular : GlobalFunctionalPieceRegular F)
    (V : Type) [Finite V] :
    Finite
      {Y : Structure (globalFunctionalPieceLanguage F) V //
        IsGlobalFiniteMaximalTrace F K Y} := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite (Structure L V) :=
    finiteNativeStructures_onFiniteCarrier L V
  letI : ∀ A : Structure L V,
      Finite (GlobalMaximalTraceExactFibre F K A) :=
    fun A => globalMaximalTraceExactFibre_finite F K hRegular A
  let codes :
      {Y : Structure (globalFunctionalPieceLanguage F) V //
        IsGlobalFiniteMaximalTrace F K Y} →
      (Σ A : Structure L V,
        GlobalMaximalTraceExactFibre F K A) :=
    fun Y =>
      ⟨functionalShadowBig L
          (GlobalFunctionalPieceSymbol F)
          (globalFunctionalPieceArity F) Y.1,
        ⟨Y.1, rfl, Y.2⟩⟩
  have hCodes : Finite
      (Σ A : Structure L V,
        GlobalMaximalTraceExactFibre F K A) := by
    infer_instance
  letI := hCodes
  apply Finite.of_injective codes
  intro Y Z h
  apply Subtype.ext
  exact congrArg
    (fun p : Σ A : Structure L V,
      GlobalMaximalTraceExactFibre F K A => p.2.1) h

end AllThoseRamseyClasses.Lifts
