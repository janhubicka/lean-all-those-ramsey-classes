import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import AllThoseRamseyClasses.Published.TrackEHybridVisibleWholeSplitAgreement
import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Structure.PartialSetFunctionsWholeMaskPatterns

/-!
# Track E2: positive hybrid output tuples imply their input domains and output part labels

The hybrid signature has two kinds of positive function-output
relations: an ORIGINAL complete multivalued output tuple, and a
SINGLETON per-output-part split function graph tuple. Arbitrary
relational Pictures may carry a positive output relation without
its corresponding input-domain relation, or with the wrong unary
vertex-part label on a displayed output. Those Pictures are NOT
canonical native functional structures.

These are four necessary semantic conditions for a normalizable
hybrid target:
  1. every complete ORIGINAL output tuple implies its exact
     corresponding active ORIGINAL full output-mask domain root;
  2. every split output incidence implies its split active domain;
  3. every split output is labelled by its designated part;
  4. each output coordinate of a complete ORIGINAL tuple is
     labelled by the corresponding mask part.

Rather than duplicating four free-amalgam case analyses, factor
through a generic relational condition TupleImpliesRoot R Q pick:
every R-tuple implies a Q-tuple on a fixed list of selected
coordinates. This condition is inherited under exact relational
induction and true FULL relational free amalgamation, since every
positive R-tuple lies on one side and full embeddings preserve Q.

The resulting HybridPositiveOutputSound predicate is true for any
canonical native partite System, hereditary on EVERY exact weak
vertex subset, and stable under FULL free amalgamation of
Pictures satisfying it. Unlike the stronger demand that every
surviving split incidence already has a VISIBLE whole output
tuple, these conditions remain valid after whole-value weak cuts.

This does NOT assert the converse that all active domains have
visible outputs on arbitrary weak subsets, nor that arbitrary
hybrid targets decode to native functions. Those are final-target
normality/closed-completion obligations. No new vertices or
function-generated closure hull are introduced.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey

universe u w
variable {K : RelLanguage.{u}}

/-- A positive R-tuple semantically forces the Q-tuple on a
specified list of selected vertices. The relation symbols may
have different arities, and the vertices may repeat. -/
def TupleImpliesRoot
    {V : Type w}
    (A : RelStructure K V)
    (R Q : K.Symbol)
    (pick : Fin (K.arity Q) → Fin (K.arity R)) : Prop :=
  ∀ t, A.rel R t → A.rel Q (t ∘ pick)

/-- Any literal exact induced vertex set inherits this positive
tuple-to-subtuple implication, with no extra closure vertices. -/
theorem TupleImpliesRoot.induce
    {V : Type w}
    {A : RelStructure K V}
    {R Q : K.Symbol}
    {pick : Fin (K.arity Q) → Fin (K.arity R)}
    (h : TupleImpliesRoot A R Q pick)
    (S : Set V) :
    TupleImpliesRoot (A.induce S) R Q pick := by
  intro t ht
  have hBase := h (Subtype.val ∘ t) ht
  have hEq :
      ((Subtype.val ∘ t) ∘ pick) =
        (Subtype.val ∘ (t ∘ pick)) := by
    funext i
    rfl
  rw [hEq] at hBase
  exact hBase

/-- A TRUE full relational free amalgam preserves any fixed
positive tuple-to-root implication of the two sides. A fresh
R-tuple necessarily comes from one side, whose Q-tuple maps into
the whole by the SAME full side embedding. -/
theorem TupleImpliesRoot.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure K H}
    {Left : RelStructure K E}
    {Right : RelStructure K F}
    {Whole : RelStructure K C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (R Q : K.Symbol)
    (pick : Fin (K.arity Q) → Fin (K.arity R))
    (hLeft : TupleImpliesRoot Left R Q pick)
    (hRight : TupleImpliesRoot Right R Q pick) :
    TupleImpliesRoot Whole R Q pick := by
  intro t ht
  rcases (hFree.rel_iff R t).mp ht with
    ⟨x, hx, htx⟩ | ⟨x, hx, htx⟩
  · have hQ := (iL.map_rel_iff Q (x ∘ pick)).mpr (hLeft x hx)
    have hEq : t ∘ pick = iL ∘ (x ∘ pick) := by
      funext k
      exact congrFun htx (pick k)
    rw [hEq]
    exact hQ
  · have hQ := (iR.map_rel_iff Q (x ∘ pick)).mpr (hRight x hx)
    have hEq : t ∘ pick = iR ∘ (x ∘ pick) := by
      funext k
      exact congrFun htx (pick k)
    rw [hEq]
    exact hQ

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The four positive-output semantic soundness conditions of the
hybrid original-mask / singleton-split graph: a visible positive
function output implies its original active input-domain relation
and the appropriate unary part-label predicates on the output
vertices. No witness for an invisible positive tuple is required. -/
def HybridPositiveOutputSound
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  (∀ (p : FunctionInputPattern L) (m : CompleteOutputParts Parts),
    TupleImpliesRoot E
      (hybridOriginalMaskOutputSymbol p m)
      (hybridOriginalMaskDomainSymbol p m)
      (fun i : Fin p.rootSize => Fin.castAdd m.size i)) ∧
  (∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
    TupleImpliesRoot E
      (hybridSplitOutputSymbol p)
      (hybridSplitDomainSymbol p)
      (fun i : Fin p.rootSize => i.castSucc)) ∧
  (∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
    TupleImpliesRoot E
      (hybridSplitOutputSymbol p)
      (.inr (.inr p.symbol.2))
      (fun _ : Fin 1 => Fin.last p.rootSize)) ∧
  (∀ (p : FunctionInputPattern L) (m : CompleteOutputParts Parts)
    (j : Fin m.size),
    TupleImpliesRoot E
      (hybridOriginalMaskOutputSymbol p m)
      (.inr (.inr (m.label j)))
      (fun _ : Fin 1 => Fin.natAdd p.rootSize j))

/-- All four soundness conditions are valid in the canonical
presentation of a genuinely native partite functional System,
including repeated input tuples and arbitrary multivalued
original output fibres. -/
theorem canonicalHybrid_positiveOutputSound
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridPositiveOutputSound A.splitMaskHybrid := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p m t ht
    exact
      A.toStructure.toNonemptyPartial.wholeMaskPatternGraph_output_has_domain
        A.part p m t ht
  · intro p t ht
    have hSplit :
        Function.Injective (fun i : Fin p.rootSize => t i.castSucc) ∧
        t (Fin.last p.rootSize) ∈
          A.splitOutputParts.toStructure.func p.symbol
            ((fun i : Fin p.rootSize => t i.castSucc) ∘ p.argMap) := ht
    change Function.Injective
        (fun i : Fin p.rootSize => t i.castSucc) ∧
      (A.splitOutputParts.toStructure.func p.symbol
        ((fun i : Fin p.rootSize => t i.castSucc) ∘
          p.argMap)).Nonempty
    exact ⟨hSplit.1, ⟨t (Fin.last p.rootSize), hSplit.2⟩⟩
  · intro p t ht
    have hSplit :
        Function.Injective (fun i : Fin p.rootSize => t i.castSucc) ∧
        t (Fin.last p.rootSize) ∈
          A.splitOutputParts.toStructure.func p.symbol
            ((fun i : Fin p.rootSize => t i.castSucc) ∘ p.argMap) := ht
    exact hSplit.2.2
  · intro p m j t ht
    have hWhole :
        Function.Injective
          (fun i : Fin p.rootSize =>
            t (Fin.castAdd m.size i)) ∧
        A.toStructure.toNonemptyPartial.func p.symbol
          ((fun i : Fin p.rootSize =>
            t (Fin.castAdd m.size i)) ∘ p.argMap) =
          some (Set.range (fun k : Fin m.size =>
            t (Fin.natAdd p.rootSize k))) ∧
        (∀ k : Fin m.size,
          A.part (t (Fin.natAdd p.rootSize k)) = m.label k) := ht
    exact hWhole.2.2 j

/-- The entire FOUR-CLAUSE package is stable on every exact
induced relational weak subset, including whole-output cuts. -/
theorem HybridPositiveOutputSound.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridPositiveOutputSound E)
    (S : Set V) :
    HybridPositiveOutputSound (E.induce S) :=
  ⟨fun p m => (h.1 p m).induce S,
   fun p => (h.2.1 p).induce S,
   fun p => (h.2.2.1 p).induce S,
   fun p m j => (h.2.2.2 p m j).induce S⟩

/-- Since each soundness law is a positive tuple-to-subtuple
implication, all four survive TRUE relational free amalgamation
of base hybrid Pictures, with no separate common-root condition. -/
theorem HybridPositiveOutputSound.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridPositiveOutputSound Left)
    (hRight : HybridPositiveOutputSound Right) :
    HybridPositiveOutputSound Whole :=
  ⟨fun p m => TupleImpliesRoot.freeAmalgam hFree
      (hybridOriginalMaskOutputSymbol p m)
      (hybridOriginalMaskDomainSymbol p m)
      (fun i : Fin p.rootSize => Fin.castAdd m.size i)
      (hLeft.1 p m) (hRight.1 p m),
   fun p => TupleImpliesRoot.freeAmalgam hFree
      (hybridSplitOutputSymbol p)
      (hybridSplitDomainSymbol p)
      (fun i : Fin p.rootSize => i.castSucc)
      (hLeft.2.1 p) (hRight.2.1 p),
   fun p => TupleImpliesRoot.freeAmalgam hFree
      (hybridSplitOutputSymbol p)
      (.inr (.inr p.symbol.2))
      (fun _ : Fin 1 => Fin.last p.rootSize)
      (hLeft.2.2.1 p) (hRight.2.2.1 p),
   fun p m j => TupleImpliesRoot.freeAmalgam hFree
      (hybridOriginalMaskOutputSymbol p m)
      (.inr (.inr (m.label j)))
      (fun _ : Fin 1 => Fin.natAdd p.rootSize j)
      (hLeft.2.2.2 p m j) (hRight.2.2.2 p m j)⟩

end StructuralRamsey.RelStructure
