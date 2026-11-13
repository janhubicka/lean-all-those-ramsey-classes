import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: active input-domain relations have genuinely distinct root vertices

A function input equality-pattern presentation contains a list of
DISTINCT input vertices and a surjective map from primitive argument
positions to that list. In the canonical hybrid of a native partite
structure, positivity of an ORIGINAL mask domain or singleton split
domain therefore requires injectivity of its displayed root tuple.

Arbitrary relational sparse Pictures need not satisfy this condition:
a nominal two-vertex pattern can otherwise be activated on (x,x),
without any valid injective full-root embedding. The full-hybrid-root
tag interpretation cannot close such a spurious tuple merely by
having exact tags and U-closedness.

The generic positive-relation tuple-injectivity predicate below is
exact-hereditary and preserved by genuine FULL relational free
amalgamation. Instantiate it for both original complete-mask domains
and singleton split domains. The resulting source invariant needs no
positive-arity assumption, no output vertices and no generated hull.

This is a NECESSARY target-normalization guard, not a decoder, a
sufficient normality criterion, or the finite-family E2 witness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language

universe u v w

variable {K : RelLanguage.{u}}

/-- Every positive tuple of the chosen relational symbol has pairwise
distinct coordinates. In particular, an active domain-root relation
cannot be assigned to a noninjective nominal distinct-input tuple. -/
def ActiveRelTuplesInjective
    {V : Type w}
    (A : RelStructure K V) (R : K.Symbol) : Prop :=
  ∀ t, A.rel R t → Function.Injective t

/-- No new noninjective active relation tuple can appear when an
ambient relational structure is restricted to an exact vertex subset. -/
theorem ActiveRelTuplesInjective.induce
    {V : Type w}
    {A : RelStructure K V} {R : K.Symbol}
    (h : ActiveRelTuplesInjective A R) (S : Set V) :
    ActiveRelTuplesInjective (A.induce S) R := by
  intro t ht i j hij
  exact h (Subtype.val ∘ t) ht (congrArg Subtype.val hij)

/-- FULL relational free amalgamation does not create noninjective
positive tuples if neither side has them: every positive tuple
comes from one side, and that side embeds injectively. -/
theorem ActiveRelTuplesInjective.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure K H}
    {Left : RelStructure K E}
    {Right : RelStructure K F}
    {Whole : RelStructure K C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (R : K.Symbol)
    (hLeft : ActiveRelTuplesInjective Left R)
    (hRight : ActiveRelTuplesInjective Right R) :
    ActiveRelTuplesInjective Whole R := by
  intro t ht
  rcases (hFree.rel_iff R t).mp ht with
    ⟨x, hx, htx⟩ | ⟨x, hx, htx⟩
  · rw [htx]
    intro i j hij
    exact hLeft x hx (iL.injective hij)
  · rw [htx]
    intro i j hij
    exact hRight x hx (iR.injective hij)

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- BOTH hybrid input-domain symbol families enforce their intended
injective DISTINCT-input root semantics. This does not assert the
existence of any output tuple or its equality with a native value. -/
def HybridActiveDomainRootInjective
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  (∀ (p : FunctionInputPattern L)
      (mask : CompleteOutputParts Parts),
    ActiveRelTuplesInjective E (hybridOriginalMaskDomainSymbol p mask)) ∧
  (∀ p : FunctionInputPattern (L.outputPartIndexed Parts),
    ActiveRelTuplesInjective E (hybridSplitDomainSymbol p))

/-- Canonical native hybrid presentations activate a domain only
on an actual injective distinct-input root. No finiteness
or positive-primitive-input assumption is needed. -/
theorem canonicalHybrid_activeDomainRootInjective
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridActiveDomainRootInjective A.splitMaskHybrid := by
  constructor
  · intro p mask root hOld
    exact hOld.1
  · intro p root hSplit
    exact hSplit.1

/-- Exact induced weak tests preserve both ORIGINAL-mask and SPLIT
input-root injectivity, independently of which outputs survive. -/
theorem HybridActiveDomainRootInjective.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridActiveDomainRootInjective E)
    (S : Set V) :
    HybridActiveDomainRootInjective (E.induce S) := by
  constructor
  · intro p mask
    exact (h.1 p mask).induce S
  · intro p
    exact (h.2 p).induce S

/-- BOTH active-input-root injectivity laws are preserved by true
FULL hybrid relational free amalgamation, without any additional
root-closure assumption. The new tuples are precisely side images. -/
theorem HybridActiveDomainRootInjective.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridActiveDomainRootInjective Left)
    (hRight : HybridActiveDomainRootInjective Right) :
    HybridActiveDomainRootInjective Whole := by
  constructor
  · intro p mask
    exact ActiveRelTuplesInjective.freeAmalgam hFree
      (hybridOriginalMaskDomainSymbol p mask)
      (hLeft.1 p mask) (hRight.1 p mask)
  · intro p
    exact ActiveRelTuplesInjective.freeAmalgam hFree
      (hybridSplitDomainSymbol p)
      (hLeft.2 p) (hRight.2 p)

end StructuralRamsey.RelStructure
