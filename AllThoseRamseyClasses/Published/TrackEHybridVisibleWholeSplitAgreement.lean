import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: conditional SAME-VALUE coherence of visible whole OLD and split output tuples

The canonical joint hybrid source has BOTH complete multivalued OLD
output tuples and individual (F,q) singleton split output graph tuples.

A genuine target must not assign a different split output of part q
than the q-coordinate of an already present complete ORIGINAL tuple.
We formulate the exact visible-tuple agreement:

For any visible ORIGINAL complete (F,output-parts) tuple, any q-slot
j, and any singleton split output tuple whose full distinct input
root equals that of the original tuple, the split graph holds IFF
its displayed output equals the original tuple's j-th output.

The proof for a genuine native partite System uses the entire
original full function value, the canonical per-part split, and
the actual transversality law. It is NOT mere output-part-mask
agreement: vertex identity, not just part equality, is checked.

This predicate is inherited by EVERY exact induced relational weak
test, even when weak restriction drops other original values. It
does NOT falsely require a complete original tuple to be visible
whenever a singleton split output survives: for F(a)={u,v} on
S={a,u}, the split incidence (a,u) survives but the complete OLD
tuple cannot, since v is outside S. The conditional predicate
correctly leaves that case unrestricted.

Free-amalgam stability of this cross-output law is deliberately NOT
claimed for arbitrary relational hybrid free diagrams: an original
whole tuple on one side and a conflicting split output on the other
can share a root unless coherent U-closed root compatibility prevents
the collision. That is an actual constrained-target class gate.

No new vertices, closure hulls, global target normalization, or
two-pass E2 Ramsey conclusion are asserted.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Visible COMPLETE original OLD output tuples agree in vertex
identity with every singleton split output graph tuple on the same
input root and corresponding output part. This is deliberately
conditional on the complete old tuple being present. -/
def HybridVisibleWholeSplitAgreement
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (m : Language.CompleteOutputParts Parts)
    (t : Fin (p.rootSize + m.size) → V)
    (j : Fin m.size)
    (u : Fin (p.rootSize + 1) → V),
    E.rel (Language.hybridOriginalMaskOutputSymbol p m) t →
    (∀ i : Fin p.rootSize,
      u i.castSucc = t (Fin.castAdd m.size i)) →
    (E.rel (Language.hybridSplitOutputSymbol
        (Language.splitMaskInputAtPart p (m.label j))) u ↔
      u (Fin.last p.rootSize) =
        t (Fin.natAdd p.rootSize j))

/-- On any genuine native partite System, an ORIGINAL complete
OLD output tuple records the entire actual function value. The
split graph for a fixed output part then denotes its unique value
of that part. No carrier finiteness or positive primitive arity
is needed for this conditional full-tuple statement. -/
theorem canonicalHybrid_visibleWholeSplitAgreement
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridVisibleWholeSplitAgreement A.splitMaskHybrid := by
  classical
  intro p m t j u hWhole hRoot
  let root : Fin p.rootSize → V :=
    fun i => t (Fin.castAdd m.size i)
  let out : Fin m.size → V :=
    fun j => t (Fin.natAdd p.rootSize j)
  have hWholeData :
      Function.Injective root ∧
      A.toStructure.toNonemptyPartial.func
        p.symbol (root ∘ p.argMap) = some (Set.range out) ∧
      (∀ j : Fin m.size, A.part (out j) = m.label j) :=
    hWhole
  obtain ⟨hInj, hValue, hLabels⟩ := hWholeData
  have hNative : A.func p.symbol (root ∘ p.argMap) =
      Set.range out := by
    change (if (A.func p.symbol (root ∘ p.argMap)).Nonempty then
      some (A.func p.symbol (root ∘ p.argMap)) else none) =
      some (Set.range out) at hValue
    by_cases hn : (A.func p.symbol (root ∘ p.argMap)).Nonempty
    · simpa [hn] using hValue
    · simp [hn] at hValue
  let uRoot : Fin p.rootSize → V :=
    fun i => u i.castSucc
  have hInput : uRoot ∘ p.argMap = root ∘ p.argMap := by
    funext k
    exact hRoot (p.argMap k)
  have hUInj : Function.Injective uRoot := by
    intro i k hik
    apply hInj
    calc
      root i = uRoot i := (hRoot i).symm
      _ = uRoot k := hik
      _ = root k := hRoot k
  have hOutMem : out j ∈ A.func p.symbol (root ∘ p.argMap) := by
    rw [hNative]
    exact ⟨j, rfl⟩
  constructor
  · intro hSplit
    have hSplitData :
        Function.Injective uRoot ∧
        (u (Fin.last p.rootSize) ∈
            A.func p.symbol (uRoot ∘ p.argMap) ∧
          A.part (u (Fin.last p.rootSize)) = m.label j) :=
      hSplit
    have hy : u (Fin.last p.rootSize) ∈
        A.func p.symbol (root ∘ p.argMap) := by
      rw [← hInput]
      exact hSplitData.2.1
    exact A.funcTransversal p.symbol (root ∘ p.argMap)
      (u (Fin.last p.rootSize)) (out j)
      hy hOutMem
      (hSplitData.2.2.trans (hLabels j).symm)
  · intro hEq
    change Function.Injective uRoot ∧
      (u (Fin.last p.rootSize) ∈
        A.func p.symbol (uRoot ∘ p.argMap) ∧
       A.part (u (Fin.last p.rootSize)) = m.label j)
    refine ⟨hUInj, ?_, ?_⟩
    · rw [hInput, hEq]
      exact hOutMem
    · rw [hEq]
      exact hLabels j

/-- The conditional SAME-VALUE coherence predicate is hereditary
under all exact relational induced weak subsets S. Only tuples
whose full vertices are ALREADY in S are tested; no output value
escaping S is spuriously required to reappear. -/
theorem HybridVisibleWholeSplitAgreement.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridVisibleWholeSplitAgreement E)
    (S : Set V) :
    HybridVisibleWholeSplitAgreement (E.induce S) := by
  intro p m t j u hOld hRoot
  let t0 : Fin (p.rootSize + m.size) → V :=
    Subtype.val ∘ t
  let u0 : Fin (p.rootSize + 1) → V :=
    Subtype.val ∘ u
  have hRoot0 : ∀ i : Fin p.rootSize,
      u0 i.castSucc = t0 (Fin.castAdd m.size i) := by
    intro i
    exact congrArg Subtype.val (hRoot i)
  have hAgreement := h p m t0 j u0 hOld hRoot0
  constructor
  · intro hSplit
    apply Subtype.ext
    exact hAgreement.mp hSplit
  · intro hEq
    apply hAgreement.mpr
    exact congrArg Subtype.val hEq

end StructuralRamsey.RelStructure
