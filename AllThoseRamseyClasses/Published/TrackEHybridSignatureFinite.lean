import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.PatternLanguageFinite
import PartiteConstruction.Functional.WholeMaskTagLanguageFinite2019

/-!
# Track E2: the full OLD/split hybrid tagged signature is FINITE

The same-carrier hybrid of Track E2 #1037 contains:
(1) the complete-output OLD/full-root tag language;
(2) the per-output-part singleton equality-pattern/full-root tags;
(3) the unary predicates for vertex parts.

The complete-output OLD tag finiteness is already verified in the
partite-construction dependency. The equality-pattern tag language
needs its own finite representation: a fresh full-root tag is
determined by an input equality pattern and an old relational
structure on the finite distinct-root carrier; the positivity and
domain fields are propositions.

We provide the faithful proof-free raw representation, derive its
finite type and injectivity, and thus prove finiteness of the
per-output-part pattern-tag language and of the WHOLE hybrid sum.

No arbitrary hybrid relational target is decoded or assumed U-closed.
Finiteness is a prerequisite for Ramsey/sparse construction, not a
proof of hybrid strong amalgamation, profile coherence or the
finite-family E2 ordered Ramsey theorem.
-/

namespace StructuralRamsey.Language

universe u v

variable {L : Language.{u}}

/-- Every finite primitive language has only finitely many
equality-pattern OLD relation symbols. The input-pattern finite
instance is supplied by the pinned PatternLanguageFinite library. -/
instance patternGraph_symbol_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.patternGraph).Symbol := by
  change Finite (L.RelSymbol ⊕
    (FunctionInputPattern L ⊕ FunctionInputPattern L))
  infer_instance

/-- Proof-free data of one full positive root pattern:
the distinct-input equality pattern and its actual old relational
root on exactly Fin rootSize. -/
def FunctionRootRaw (L : Language.{u}) :=
  Σ pat : FunctionInputPattern L,
    RelStructure L.patternGraph (Fin pat.rootSize)

/-- Forget only proof fields (positive root and active domain), not
the full induced OLD relational root. -/
def FunctionRootPattern.toRaw
    (p : FunctionRootPattern L) : FunctionRootRaw L :=
  ⟨p.input, p.root⟩

/-- The raw representation is injective: proofs are irrelevant. -/
theorem FunctionRootPattern.toRaw_injective :
    Function.Injective
      (FunctionRootPattern.toRaw :
        FunctionRootPattern L → FunctionRootRaw L) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- An arbitrary input pattern has finite distinct-root carrier,
so there are finitely many OLD relational patterns on it. -/
instance functionRootRaw_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (FunctionRootRaw L) := by
  classical
  unfold FunctionRootRaw
  infer_instance

/-- Full-root equality-pattern tags form a finite type,
including every genuine induced OLD root pattern. -/
instance functionRootPattern_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (FunctionRootPattern L) :=
  Finite.of_injective FunctionRootPattern.toRaw
    FunctionRootPattern.toRaw_injective

/-- The canonical equality-pattern full-root tagged language is finite
for any primitive language with finite relation/function symbols. -/
instance patternTag_symbol_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.patternTag).Symbol := by
  change Finite ((L.patternGraph).Symbol ⊕ FunctionRootPattern L)
  infer_instance

/-- Output-part splitting preserves finiteness of primitive
relation and function symbol types: the indexed functions are F×P. -/
instance outputPartIndexed_relSymbol_finite
    (L : Language.{u}) (P : Type v)
    [Finite L.RelSymbol] :
    Finite (L.outputPartIndexed P).RelSymbol := by
  change Finite (ULift.{max u v, u} L.RelSymbol)
  infer_instance

instance outputPartIndexed_funcSymbol_finite
    (L : Language.{u}) (P : Type v)
    [Finite L.FuncSymbol] [Finite P] :
    Finite (L.outputPartIndexed P).FuncSymbol := by
  change Finite (ULift.{max u v, u} L.FuncSymbol × P)
  infer_instance

/-- FINITE hybrid signature: complete original output masks with
their full-root tags, singleton split output incidences with their
full-root tags, and unary vertex parts. No boundedness of the
carrier's function fibres beyond the finite part set is required. -/
instance splitMaskHybrid_symbol_finite
    (L : Language.{u}) (P : Type v)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.splitMaskHybrid P).Symbol := by
  classical
  change Finite ((L.wholeMaskTagLanguage P).Symbol ⊕
    (((L.outputPartIndexed P).patternTag).Symbol ⊕ P))
  infer_instance

/-- Named theorem root for exact-head axiom audit and downstream
finite-relational Ramsey library interfaces. -/
theorem splitMaskHybrid_signature_finite
    (L : Language.{u}) (P : Type v)
    [Fintype P] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.splitMaskHybrid P).Symbol :=
  inferInstance

end StructuralRamsey.Language
