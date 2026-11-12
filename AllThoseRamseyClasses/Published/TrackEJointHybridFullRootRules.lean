import AllThoseRamseyClasses.Published.TrackEHybridFullSplitRootTags
import PartiteConstruction.Functional.WholeMaskTagLanguageFinite2019

/-!
# Track E2: one JOINT hybrid full-root closure description

A full hybrid picture must protect TWO kinds of function information
on its exact weak tests: every surviving per-output-part singleton
incidence and every original complete multivalued output-part mask.
Independent OLD tags were generated in smaller languages, so their
root names can disagree on the surrounding hybrid pattern.

We now define BOTH new closure tag families over a SINGLE base
hybrid source language, indexing every tag by the complete HYBRID
root relational pattern on the same finite distinct-input carrier:

* SplitRoot: a positive (F,q) singleton-output incidence with the
  full hybrid input-root pattern and its split-domain relation.
* MaskRoot: a positive complete original multivalued output-mask
  tuple, with the full hybrid input-root pattern and its original
  complete output-part domain mask.

The two kinds of fresh tags share a SINGLE joint outer language
and a SINGLE 2019 closure description. Both types of closure rules
have properly irreducible full hybrid roots, witnessed directly
by the OLD domain relation spanning every distinct input-root
coordinate. We also verify FINITENESS of all tag names and thus
of the entire joint expanded signature.

This is the common syntactic closure environment required by a
genuine 2019 hybrid sparse construction. Source-side U-closedness,
strong amalgamation, target decoding, HE protection and the actual
finite-family ordered Ramsey witness remain separate proof gates.
-/

namespace StructuralRamsey.Language

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The original complete multivalued function domain mask is a
HYBRID old relation, not one of the singleton split domains.
Its input equality pattern is in the PART-PREDICATE expansion. -/
def hybridOriginalMaskDomainSymbol
    (p : FunctionInputPattern (L.withParts Parts))
    (q : CompleteOutputParts Parts) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inl (.inl (.inr (.inl (p, q))))

/-- The old complete output tuple is ONE relation enumerating the
ENTIRE source fibre with its distinct output parts. It is not an
individual incidence relation. -/
def hybridOriginalMaskOutputSymbol
    (p : FunctionInputPattern (L.withParts Parts))
    (q : CompleteOutputParts Parts) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inl (.inl (.inr (.inr (p, q))))

/-- A fresh ROOT-TAG name for a defined original multivalued output:
the full hybrid relational root is stored on the distinct input
vertices, including all ORIGINAL masks, split incidences and
vertex-part predicates already present within the root. -/
structure OriginalMaskHybridRootPattern
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] where
  input : FunctionInputPattern (L.withParts Parts)
  mask : CompleteOutputParts Parts
  rootPositive : 0 < input.rootSize
  outputPositive : 0 < mask.size
  root : RelStructure (L.splitMaskHybrid Parts) (Fin input.rootSize)
  hasDomain : root.rel (hybridOriginalMaskDomainSymbol input mask) id

/-- Two independent full-root tag families indexed over ONE full
hybrid OLD source language; old-mask and singleton-incidence tags
cannot be confused by a later profile or weak induction. -/
def splitMaskJointRootLanguage
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] :
    RelLanguage.{max u v} where
  Symbol := (L.splitMaskHybrid Parts).Symbol ⊕
    (SplitMaskFullRootPattern L Parts ⊕
      OriginalMaskHybridRootPattern L Parts)
  arity
    | .inl R => (L.splitMaskHybrid Parts).arity R
    | .inr (.inl p) => p.input.rootSize + 1
    | .inr (.inr p) => p.input.rootSize + p.mask.size

/-- Proof-free complete HYBRID raw root data for an original mask
tag. The positivity/domain fields of the tag name are propositions. -/
def OriginalMaskHybridRootRaw (L : Language.{u})
    (Parts : Type v) [Fintype Parts] :=
  Σ (p : FunctionInputPattern (L.withParts Parts)),
    Σ (q : CompleteOutputParts Parts),
      RelStructure (L.splitMaskHybrid Parts) (Fin p.rootSize)

def OriginalMaskHybridRootPattern.toRaw
    (p : OriginalMaskHybridRootPattern L Parts) :
    OriginalMaskHybridRootRaw L Parts :=
  ⟨p.input, p.mask, p.root⟩

theorem OriginalMaskHybridRootPattern.toRaw_injective :
    Function.Injective
      (OriginalMaskHybridRootPattern.toRaw :
        OriginalMaskHybridRootPattern L Parts →
          OriginalMaskHybridRootRaw L Parts) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- Every positive singleton full hybrid root pattern has only
a finite choice of input equality pattern and full hybrid
relational root, once the original signature and parts are finite. -/
def SplitMaskFullRootRaw (L : Language.{u})
    (Parts : Type v) [Fintype Parts] :=
  Σ (p : FunctionInputPattern (L.outputPartIndexed Parts)),
    RelStructure (L.splitMaskHybrid Parts) (Fin p.rootSize)

def SplitMaskFullRootPattern.toRaw
    (p : SplitMaskFullRootPattern L Parts) :
    SplitMaskFullRootRaw L Parts :=
  ⟨p.input, p.root⟩

theorem SplitMaskFullRootPattern.toRaw_injective :
    Function.Injective
      (SplitMaskFullRootPattern.toRaw :
        SplitMaskFullRootPattern L Parts →
          SplitMaskFullRootRaw L Parts) := by
  intro a b h
  cases a
  cases b
  cases h
  rfl

/-- Original part-predicate language remains finite. -/
instance withParts_hybrid_rel_finite
    [Finite L.RelSymbol] :
    Finite (L.withParts Parts).RelSymbol := by
  change Finite (ULift.{max u v, u} L.RelSymbol ⊕ Parts)
  infer_instance

instance withParts_hybrid_func_finite
    [Finite L.FuncSymbol] :
    Finite (L.withParts Parts).FuncSymbol := by
  change Finite (ULift.{max u v, u} L.FuncSymbol)
  infer_instance

instance splitMaskFullRootRaw_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (SplitMaskFullRootRaw L Parts) := by
  classical
  unfold SplitMaskFullRootRaw
  infer_instance

instance splitMaskFullRootPattern_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (SplitMaskFullRootPattern L Parts) :=
  Finite.of_injective SplitMaskFullRootPattern.toRaw
    SplitMaskFullRootPattern.toRaw_injective

instance originalMaskHybridRootRaw_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (OriginalMaskHybridRootRaw L Parts) := by
  classical
  unfold OriginalMaskHybridRootRaw
  infer_instance

instance originalMaskHybridRootPattern_finite
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (OriginalMaskHybridRootPattern L Parts) :=
  Finite.of_injective OriginalMaskHybridRootPattern.toRaw
    OriginalMaskHybridRootPattern.toRaw_injective

/-- The JOINT full hybrid-root language is finite. This includes
all hybrid base symbols plus BOTH families of root-pattern tags,
not merely the original half of the syntax. -/
instance splitMaskJointRoot_symbol_finite
    (L : Language.{u}) (Parts : Type v)
    [Fintype Parts] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.splitMaskJointRootLanguage Parts).Symbol := by
  classical
  change Finite ((L.splitMaskHybrid Parts).Symbol ⊕
    (SplitMaskFullRootPattern L Parts ⊕
      OriginalMaskHybridRootPattern L Parts))
  infer_instance

theorem splitMaskJointRoot_signature_finite
    (L : Language.{u}) (Parts : Type v)
    [Fintype Parts] [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    Finite (L.splitMaskJointRootLanguage Parts).Symbol :=
  inferInstance

end StructuralRamsey.Language

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Interpret BOTH full-hybrid-root tag types at once, on the EXACT
same vertex carrier of a hybrid relational source E. Each tag
requires a positive old tuple and the entire named hybrid input
root to embed on the displayed input prefix. -/
def splitMaskJointRootExpansion
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure (L.splitMaskJointRootLanguage Parts) V where
  rel
    | .inl R, xs => E.rel R xs
    | .inr (.inl p), xs =>
        E.rel (Language.hybridSplitOutputSymbol p.input) xs ∧
          ∃ e : Embedding p.root E,
            ∀ i : Fin p.input.rootSize, xs i.castSucc = e i
    | .inr (.inr p), xs =>
        E.rel (Language.hybridOriginalMaskOutputSymbol
          p.input p.mask) xs ∧
          ∃ e : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs (Fin.castAdd p.mask.size i) = e i

/-- The joint full-root expansion forgets back to exactly the original
hybrid source, not a generated closure hull or a different vertex set. -/
def splitMaskJointRootReduct
    (E : RelStructure (L.splitMaskJointRootLanguage Parts) V) :
    RelStructure (L.splitMaskHybrid Parts) V where
  rel R xs := E.rel (.inl R) xs

theorem splitMaskJointRoot_reduct_canonical
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    splitMaskJointRootReduct (splitMaskJointRootExpansion E) = E := rfl

end StructuralRamsey.RelStructure

namespace StructuralRamsey.Language.SplitMaskFullRootPattern

open StructuralRamsey.RelStructure
universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The SPLIT family of genuine closure rules in the JOINT hybrid
tag language. The active split domain spans the full root and
witnesses ordinary root irreducibility. -/
def jointClosureRule (p : SplitMaskFullRootPattern L Parts) :
    ClosureRule (L.splitMaskJointRootLanguage Parts) where
  symbol := .inr (.inl p)
  rootSize := p.input.rootSize
  rootPositive := p.positive
  rootStrict := Nat.lt_succ_self _
  root := splitMaskJointRootExpansion p.root
  rootIrreducible := by
    intro x y hxy
    refine ⟨.inl (hybridSplitDomainSymbol p.input),
      (fun i : Fin p.input.rootSize => i), x, y, ?_, rfl, rfl⟩
    exact p.hasDomain

end StructuralRamsey.Language.SplitMaskFullRootPattern

namespace StructuralRamsey.Language.OriginalMaskHybridRootPattern

open StructuralRamsey.RelStructure
universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The COMPLETE original multivalued output-mask closure rule
within the JOINT hybrid language. The root is the full HYBRID
induced input pattern, irreducible through its active old
complete-output-part domain relation. -/
def jointClosureRule (p : OriginalMaskHybridRootPattern L Parts) :
    ClosureRule (L.splitMaskJointRootLanguage Parts) where
  symbol := .inr (.inr p)
  rootSize := p.input.rootSize
  rootPositive := p.rootPositive
  rootStrict := by
    change p.input.rootSize < p.input.rootSize + p.mask.size
    omega
  root := splitMaskJointRootExpansion p.root
  rootIrreducible := by
    intro x y hxy
    refine ⟨.inl (hybridOriginalMaskDomainSymbol p.input p.mask),
      (fun i : Fin p.input.rootSize => i), x, y, ?_, rfl, rfl⟩
    exact p.hasDomain

end StructuralRamsey.Language.OriginalMaskHybridRootPattern

namespace StructuralRamsey.Language

universe u v

/-- The joint 2019 closure description contains BOTH the positive
split-function and the complete original output-mask full-hybrid
root rules, in ONE language whose symbols are finite when the
primitive signature and part set are finite. -/
def splitMaskJointClosureRules
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] :
    RelStructure.ClosureDescription
      (L.splitMaskJointRootLanguage Parts) :=
  Set.range SplitMaskFullRootPattern.jointClosureRule ∪
    Set.range OriginalMaskHybridRootPattern.jointClosureRule

end StructuralRamsey.Language
