import AllThoseRamseyClasses.Lifts.GlobalOriginalTraceLimitFiniteTupleStage
import AllThoseRamseyClasses.Lifts.GlobalFairNativeLimitAgeCofinality

/-!
# Track F: FULL finite-stage factorization and exact finite-age equality of the native limit

Mathlib's genuine first-order direct limit represents every
FINITE family of vertices together in a single finite original
maximal-trace stage (#943). The full stage-to-limit embeddings
are constructed by the function-closed image argument (#919/#930).

This module combines those results. A FULL embedding of a
finite functional structure Y into the native direct limit
factors through a FULL finite-stage embedding Y ↪ X_n.
In particular this is stronger than factoring the vertex
map: it transports the ENTIRE set-valued function output
set back through the injective full stage-to-limit map.

Heredity of the certified original maximal-trace finite age
then gives the reverse age inclusion. Combined with actual
fair finite-chain cofinality (#932/#941), this identifies the
finite FULL age of the decoded fair limit exactly.

This is a PROPOSED Lean formalization and depends on
the independent pending kernel checks of #919/#930/#941/#943.
It is NOT a claim of finite-extension property,
ultrahomogeneity, general shadow-free amalgamation or the
published Ramsey theorem. The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any FULL embedding of a finite native functional structure
into the genuine decoded direct limit factors FULLY through
one actual finite maximal-trace stage.

The proof uses the exact common-vertex-stage factorization
and cancellation by the FULL injective inclusion X_n ↪ M.
Complete function fibres are reflected, not just positive
graph relation incidences. -/
theorem globalOriginalTraceNativeLimit_finiteFullFactor
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    {V : Type} [Finite V]
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (j : Structure.Embedding Y
      (globalOriginalTraceNativeDirectLimitModel
        F hInput representatives diagrams)) :
    ∃ (n : ℕ)
      (e : Structure.Embedding Y
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams n).model),
      ∀ v : V,
        (globalOriginalTraceFullLimitIncl
          F hInput representatives diagrams n) (e v) = j v := by
  classical
  obtain ⟨n, ys, hys⟩ :=
    globalOriginalTraceFirstOrderLimit_finiteTuple_commonStage
      F hInput representatives diagrams (fun v : V => j v)
  let u := globalOriginalTraceFullLimitIncl
    F hInput representatives diagrams n
  have hu (v : V) : u (ys v) = j v := by
    calc
      u (ys v) =
        globalOriginalTraceFirstOrderLimitIncl
          F hInput representatives diagrams n (ys v) :=
        globalOriginalTraceFullLimitIncl_apply
          F hInput representatives diagrams n (ys v)
      _ = j v := hys v
  have hInj : Function.Injective ys := by
    intro a b hab
    apply j.injective
    calc
      j a = u (ys a) := (hu a).symm
      _ = u (ys b) := congrArg u hab
      _ = j b := hu b
  let e : Structure.Embedding Y
      (globalOriginalFiniteTraceChain
        F hInput representatives diagrams n).model := {
    toFun := ys
    injective := hInj
    map_rel_iff := by
      intro S xs
      have hxs : u ∘ (ys ∘ xs) = j ∘ xs := by
        funext i
        exact hu (xs i)
      have hRel := u.map_rel_iff S (ys ∘ xs)
      rw [hxs] at hRel
      exact hRel.symm.trans (j.map_rel_iff S xs)
    map_func := by
      intro S xs
      have hxs : u ∘ (ys ∘ xs) = j ∘ xs := by
        funext i
        exact hu (xs i)
      ext w
      constructor
      · rintro ⟨a, ha, rfl⟩
        have hja : j a ∈
            (globalOriginalTraceNativeDirectLimitModel
              F hInput representatives diagrams).func S (j ∘ xs) := by
          rw [← j.map_func S xs]
          exact ⟨a, ha, rfl⟩
        have hua : u (ys a) ∈
            (globalOriginalTraceNativeDirectLimitModel
              F hInput representatives diagrams).func S
              (u ∘ (ys ∘ xs)) := by
          rw [hxs]
          rwa [hu a]
        rw [← u.map_func S (ys ∘ xs)] at hua
        obtain ⟨z, hz, hza⟩ := hua
        have hza' : z = ys a := u.injective hza
        simpa only [hza'] using hz
      · intro hw
        have huw : u w ∈
            (globalOriginalTraceNativeDirectLimitModel
              F hInput representatives diagrams).func S
              (u ∘ (ys ∘ xs)) := by
          rw [← u.map_func S (ys ∘ xs)]
          exact ⟨w, hw, rfl⟩
        have hjw : u w ∈
            (globalOriginalTraceNativeDirectLimitModel
              F hInput representatives diagrams).func S
              (j ∘ xs) := by
          simpa only [hxs] using huw
        rw [← j.map_func S xs] at hjw
        obtain ⟨a, ha, haw⟩ := hjw
        exact ⟨a, ha, u.injective ((hu a).trans haw)⟩
  }
  exact ⟨n, e, hu⟩

/-- Every FINITE FULL substructure of the actual decoded native
limit belongs to the original maximal-trace finite age.

This is the reverse age direction; it uses honest finite
full-stage factorization plus genuine hereditary age
membership, without a hidden closure-hull completion. -/
theorem globalOriginalTraceNativeLimit_finiteFullAge
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    {V : Type} [Finite V]
    (Y : Structure (globalFunctionalPieceLanguage F) V)
    (j : Structure.Embedding Y
      (globalOriginalTraceNativeDirectLimitModel
        F hInput representatives diagrams)) :
    IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) Y := by
  obtain ⟨n, e, _⟩ :=
    globalOriginalTraceNativeLimit_finiteFullFactor
      F hInput representatives diagrams Y j
  exact hInput.finiteAgeCore.hereditary e
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).member

/-- EXACT finite FULL age equality of the actual fair native
functional limit, conditional on the original finite-age
Fraïssé input. The converse direction relies on factoring
finite full embeddings through finite FULL age stages.

This theorem concerns FULL functional substructures and
does not assert homogeneity, the extension property,
or removal of the outstanding original shadow-avoidance
hypothesis for reducible connected forbidden families. -/
theorem globalOriginalActualFairNativeLimit_finiteAge_iff
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {V : Type} [Finite V]
    (Y : Structure (globalFunctionalPieceLanguage F) V) :
    IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN F A) Y ↔
      Nonempty (Structure.Embedding Y
        (globalOriginalActualFairNativeLimit F hInput)) := by
  constructor
  · intro hY
    obtain ⟨j, _⟩ :=
      globalOriginalActualFairNativeLimit_contains_fullAge F hInput Y hY
    exact ⟨j⟩
  · rintro ⟨j⟩
    exact globalOriginalTraceNativeLimit_finiteFullAge
      F hInput
      (globalOriginalRepresentativePrefix F hInput)
      (globalOriginalExtensionDiagramPrefix F hInput)
      Y j

end AllThoseRamseyClasses.Lifts
