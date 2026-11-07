import AllThoseRamseyClasses.Lifts.GlobalFiniteTraceChainCoherence
import Mathlib.Order.DirectedInverseSystem

/-!
# Track F: construct the actual countable direct-limit CARRIER

The genuine original maximal-trace finite chain is already
constructed from full structural JEP/strong AP. Its all-stage
maps are actual FULL functional embeddings. Their coherence
is the separate upstream theorem in Track F PR #857.

This module turns those maps into a directed system of underlying
vertex types, forms the actual quotient direct-limit CARRIER, and
provides canonical stage-inclusion functions. The quotient is not
postulated. It is countable because each stage is finite.

No relation or function interpretation is introduced on this
carrier in this module: that further step must show that ALL
function-value fibres are stable, and must prove the canonical
stage maps are genuine FULL functional embeddings into the
interpreted limit. A bare relational-colimit embedding cannot
replace that assertion.

The entire construction is conditional on the previously
verified original finite-age input record, which still
retains the missing general shadow-avoidance hypothesis.
The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Carrier of one ACTUAL finite original global maximal-trace
chain stage. The carrier type may vary at every stage. -/
abbrev GlobalOriginalTraceStageVertex
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) : Type :=
  (globalOriginalFiniteTraceChain
    F hInput representatives diagrams n).Carrier

/-- Underlying vertex function of the already constructed
FULL structural transition embedding from stage m to n. -/
noncomputable def globalOriginalTraceStageMap
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n) :
    GlobalOriginalTraceStageVertex
      F hInput representatives diagrams m ↪
    GlobalOriginalTraceStageVertex
      F hInput representatives diagrams n where
  toFun := globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams m n h
  inj' := (globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams m n h).injective

/-- Actual coherence, identity, and composition of the vertex
transition system. The proof uses genuine full embedding
coherence from #857, not a weak image map or additional axiom. -/
instance globalOriginalTraceStage_directedSystem
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    DirectedSystem
      (fun n : ℕ => GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n)
      (fun m n h => globalOriginalTraceStageMap
        F hInput representatives diagrams m n h) where
  map_self := by
    intro i x
    change (globalOriginalFiniteTraceChainLE
      F hInput representatives diagrams i i (le_refl i)) x = x
    rw [globalOriginalFiniteTraceChainLE_self]
    rfl
  map_map := by
    intro k j i hij hjk x
    change
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams j k hjk)
        ((globalOriginalFiniteTraceChainLE
          F hInput representatives diagrams i j hij) x) =
      (globalOriginalFiniteTraceChainLE
        F hInput representatives diagrams i k
        (le_trans hij hjk)) x
    exact congrArg
      (fun e : Structure.Embedding
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams i).model
        (globalOriginalFiniteTraceChain
          F hInput representatives diagrams k).model => e x)
      (globalOriginalFiniteTraceChainLE_comp
        F hInput representatives diagrams i j k hij hjk)

/-- The actual QUOTIENT direct-limit type of all finite
stage vertices under eventual equality. No structure on
this quotient has been assumed or invented. -/
abbrev GlobalOriginalTraceDirectLimitCarrier
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :=
  DirectLimit
    (fun n : ℕ => GlobalOriginalTraceStageVertex
      F hInput representatives diagrams n)
    (fun m n h => globalOriginalTraceStageMap
      F hInput representatives diagrams m n h)

/-- Actual canonical inclusion from each finite stage into
the quotient direct-limit CARRIER. -/
noncomputable def globalOriginalTraceDirectLimitIncl
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    GlobalOriginalTraceStageVertex
      F hInput representatives diagrams n →
    GlobalOriginalTraceDirectLimitCarrier
      F hInput representatives diagrams :=
  fun x => ⟦⟨n, x⟩⟧

/-- Every canonical finite-stage inclusion is INJECTIVE,
because all old-to-new transition maps are genuine
full structural embeddings. -/
theorem globalOriginalTraceDirectLimitIncl_injective
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (n : ℕ) :
    Function.Injective
      (globalOriginalTraceDirectLimitIncl
        F hInput representatives diagrams n) := by
  apply DirectLimit.mk_injective
    (f := fun i j hij => globalOriginalTraceStageMap
      F hInput representatives diagrams i j hij)
  intro i j hij
  exact (globalOriginalFiniteTraceChainLE
    F hInput representatives diagrams i j hij).injective

/-- The quotient inclusion agrees with each full finite
transition embedding; no vertex is reinterpreted when
passing to a later stage. -/
theorem globalOriginalTraceDirectLimitIncl_comp
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F))
    (m n : ℕ) (h : m ≤ n)
    (x : GlobalOriginalTraceStageVertex
      F hInput representatives diagrams m) :
    globalOriginalTraceDirectLimitIncl
      F hInput representatives diagrams n
        (globalOriginalTraceStageMap
          F hInput representatives diagrams m n h x) =
    globalOriginalTraceDirectLimitIncl
      F hInput representatives diagrams m x := by
  exact DirectLimit.mk_apply
    (f := fun i j hij => globalOriginalTraceStageMap
      F hInput representatives diagrams i j hij)
    m n x h

/-- The genuinely constructed direct-limit CARRIER is
COUNTABLE, because it is a quotient of a countable
dependent union of finite stage-carrier types. This
does not imply homogeneity before a full functional
structure and the finite-extension property are proved. -/
theorem globalOriginalTraceDirectLimitCarrier_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    (representatives : ℕ → List (GlobalOriginalFiniteTraceRepresentatives F))
    (diagrams : ℕ → List (GlobalOriginalFiniteTraceDiagram F)) :
    Countable
      (GlobalOriginalTraceDirectLimitCarrier
        F hInput representatives diagrams) := by
  classical
  letI (n : ℕ) :
      Finite (GlobalOriginalTraceStageVertex
        F hInput representatives diagrams n) :=
    (globalOriginalFiniteTraceChain
      F hInput representatives diagrams n).member.1
  infer_instance

end AllThoseRamseyClasses.Lifts
