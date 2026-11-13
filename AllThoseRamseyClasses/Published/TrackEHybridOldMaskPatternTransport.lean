import AllThoseRamseyClasses.Published.TrackEHybridOldDomainCoherence
import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules

/-!
# Track E2: ORIGINAL complete output masks are independent of input-root enumeration

A primitive function application F(xs) has a unique SET of
distinct input vertices, but an equality-pattern presentation
may list these vertices in several different orders. Two
different surjective argument maps with INJECTIVE root lists
can therefore represent the exact same original primitive
argument tuple xs. In an arbitrary relational hybrid Picture
these two input-root presentations might carry incompatible
OLD complete-output-part domain information.

The earlier mask-coherence theorem controls two masks attached
to the SAME equality-pattern root. Here we add the separate
CROSS-PATTERN transport law: if the original mask m is active
at one exact root and another injective distinct-input root
enumerates the same primitive argument tuple, the SAME mask m
must also be active there.

The canonical genuine native partite source satisfies this
literally because both OLD masks refer to the exact same
Option(Set) primitive function value and the same output-part
map; there is no choice of a separate completion. The law is
inherited by arbitrary EXACT induced weak subsets, since all
domain predicates retain their original ambient interpretation,
even when complete output tuples escape the weak subset.

No assumption that a noninjective spurious root enumeration is
valid is made: injectivity of the second root is explicit. This
law is distinct from mere uniqueness of active mask sets on a
fixed p, and is an essential target normalization requirement
for genuinely single-valued interpretation of ORIGINAL input
tuples across the full finite 2019 pattern signature.

This module does not assert free-amalgamation stability; that
separate side-factorization step will be formalized next. It
does not construct a sparse Ramsey picture or decode arbitrary
noncanonical hybrid targets.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Same ORIGINAL complete output-part mask is transported to
every other exact injective equality-pattern root enumerating
the SAME primitive function input tuple F(xs). Primitive function
arity may be zero; no positive-root convention is needed for
this purely OLD domain predicate. -/
def HybridOldMaskPatternTransport
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → V)
    (rootB : Fin n → V)
    (mask : CompleteOutputParts Parts),
    Function.Injective rootB →
    rootA ∘ r = rootB ∘ s →
    E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, m, r, hr⟩ : FunctionInputPattern L) mask) rootA →
    E.rel (hybridOriginalMaskDomainSymbol
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) mask) rootB

/-- The canonical hybrid of any genuine native partite System
transports the SAME original mask to any alternative injective
enumeration of the same original input tuple. The entire
Option(Set) function value and actual output part set are
unchanged; repeated primitive input coordinates are supported. -/
theorem canonicalHybrid_oldMaskPatternTransport
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridOldMaskPatternTransport A.splitMaskHybrid := by
  intro F m n r s hr hs rootA rootB mask hInjB hArgs hOld
  have hSource :
      Function.Injective rootA ∧
      ∃ U : Set V,
        A.toStructure.toNonemptyPartial.func F (rootA ∘ r) =
          some U ∧
        A.part '' U = Set.range mask.label := by
    exact hOld
  obtain ⟨_hInjA, U, hValue, hMask⟩ := hSource
  change Function.Injective rootB ∧
    ∃ U : Set V,
      A.toStructure.toNonemptyPartial.func F (rootB ∘ s) =
        some U ∧
      A.part '' U = Set.range mask.label
  refine ⟨hInjB, U, ?_, hMask⟩
  rw [← hArgs]
  exact hValue

/-- CROSS-PATTERN original-mask transport remains valid after any
literal exact weak induced subset S: a newly chosen injective
enumeration of the same ambient input vertices still has the
same originally active complete output-PART mask, even when the
output tuple itself has been deleted by the weak cut. -/
theorem HybridOldMaskPatternTransport.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridOldMaskPatternTransport E) (S : Set V) :
    HybridOldMaskPatternTransport (E.induce S) := by
  intro F m n r s hr hs rootA rootB mask hInjB hArgs hOld
  have hInjBV : Function.Injective (Subtype.val ∘ rootB) := by
    intro i j hij
    apply hInjB
    exact Subtype.ext hij
  have hArgsV :
      (Subtype.val ∘ rootA) ∘ r =
        (Subtype.val ∘ rootB) ∘ s := by
    funext i
    exact congrArg Subtype.val (congrFun hArgs i)
  exact h F m n r s hr hs
    (Subtype.val ∘ rootA) (Subtype.val ∘ rootB)
    mask hInjBV hArgsV hOld

end StructuralRamsey.RelStructure
