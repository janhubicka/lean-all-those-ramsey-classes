import AllThoseRamseyClasses.Published.TrackEJointHybridNativeIrreducible

/-!
# Track E2: EXACT native function closure iff JOINT full-hybrid-root U-substructure

On the ACTUAL canonical joint-tagged hybrid representation of a
genuine partite native function structure A, a vertex subset S
is closed under ALL original multivalued function outputs IFF
the induced relational structure on the very same S is a relative
U-substructure under both fresh full-hybrid-root rule families.

The reverse implication is #1112: every original primitive function
incidence has a fresh split tag whose root is the COMPLETE hybrid
pattern on the distinct displayed input vertices.

This module proves the forward direction for BOTH rule families:
  split full-root tag: its output y lies in the ORIGINAL F-value,
  so function-closedness forces y into S;
  complete original mask tag: its displayed outputs enumerate the
  ENTIRE original function value, so all outputs are forced into S.
Both are exactly U-substructure closure, not an invented target
fibre-completion property. Repeated primitive inputs are allowed.
The positive-arity hypothesis is needed only for the reverse
direction, where the 2019 root must have positive cardinality.

By the already merged joint canonical U-closedness and the 2019
closed-induce/U-substructure theorem, native closed S is EQUIVALENT
to intrinsic U-closedness of the exact induced JOINT tagged source
on S. No generated closure hull, weakening of complete mask
domains, or arbitrary noncanonical target decoding is used.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Complete bi-implication for EXACT native closedness versus
relative JOINT full-hybrid-root U-substructure of the canonical
partite source. Neither side changes the underlying set of vertices
or the original (potentially multivalued) function fibres. -/
theorem nativeClosed_iff_jointHybridUSubstructure
    (A : FunctionalPartite.System L Parts V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) :
    A.toStructure.IsClosed S ↔
      IsUSubstructure (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion A.splitMaskHybrid) S := by
  classical
  constructor
  · intro hClosed rule hRule t hTag hRoot j
    rcases hRule with hSplit | hMask
    · obtain ⟨p, rfl⟩ := hSplit
      have hInput :
          ∀ i : Fin p.input.rootSize, t i.castSucc ∈ S := by
        intro i
        have hIndex :
            i.castLE p.jointClosureRule.rootLE = i.castSucc := by
          apply Fin.ext
          rfl
        rw [← hIndex]
        exact hRoot i
      have hSplitGraph :
          Function.Injective
            (fun i : Fin p.input.rootSize => t i.castSucc) ∧
          t (Fin.last p.input.rootSize) ∈
            A.splitOutputParts.toStructure.func p.input.symbol
              ((fun i : Fin p.input.rootSize =>
                t i.castSucc) ∘ p.input.argMap) := by
        exact hTag.1
      have hNativeOutput :
          t (Fin.last p.input.rootSize) ∈
            A.func p.input.symbol.1.down
              ((fun i : Fin p.input.rootSize =>
                t i.castSucc) ∘ p.input.argMap) :=
        hSplitGraph.2.1
      have hLast : t (Fin.last p.input.rootSize) ∈ S :=
        hClosed p.input.symbol.1.down
          ((fun i : Fin p.input.rootSize =>
            t i.castSucc) ∘ p.input.argMap)
          (fun k => hInput (p.input.argMap k)) hNativeOutput
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact hLast
      · exact hInput i
    · obtain ⟨p, rfl⟩ := hMask
      let input : Fin p.input.rootSize → V :=
        fun i => t (Fin.castAdd p.mask.size i)
      let output : Fin p.mask.size → V :=
        fun i => t (Fin.natAdd p.input.rootSize i)
      have hInput :
          ∀ i : Fin p.input.rootSize, input i ∈ S := by
        intro i
        have hIndex :
            i.castLE p.jointClosureRule.rootLE =
              Fin.castAdd p.mask.size i := by
          apply Fin.ext
          rfl
        rw [← hIndex]
        exact hRoot i
      have hValue :
          A.toStructure.toNonemptyPartial.func
            p.input.symbol (input ∘ p.input.argMap) =
              some (Set.range output) := by
        exact hTag.1.2.1
      have hNativeValue :
          A.func p.input.symbol (input ∘ p.input.argMap) =
            Set.range output := by
        change (if
            (A.func p.input.symbol
              (input ∘ p.input.argMap)).Nonempty then
            some (A.func p.input.symbol
              (input ∘ p.input.argMap)) else none) =
            some (Set.range output) at hValue
        by_cases hn :
            (A.func p.input.symbol
              (input ∘ p.input.argMap)).Nonempty
        · simpa only [if_pos hn, Option.some.injEq] using hValue
        · simp only [if_neg hn] at hValue
          cases hValue
      refine Fin.addCases ?_ ?_ j
      · intro i
        exact hInput i
      · intro i
        have hMem : output i ∈
            A.func p.input.symbol (input ∘ p.input.argMap) := by
          rw [hNativeValue]
          exact ⟨i, rfl⟩
        exact hClosed p.input.symbol
          (input ∘ p.input.argMap)
          (fun k => hInput (p.input.argMap k)) hMem
  · exact nativeClosed_of_jointHybridUSubstructure A hPos S

/-- Exact 2019 closed-substructure dictionary for the CANONICAL
joint-tagged representation: a native function-closed S has
a U-CLOSED induced hybrid source on EXACTLY S, and conversely.

The induced ambient hybrid retains OLD domain masks even if
primitive weak functions would discard outputs outside S. -/
theorem nativeClosed_iff_jointHybridInduceUClosed
    (A : FunctionalPartite.System L Parts V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V) :
    A.toStructure.IsClosed S ↔
      IsUClosed (L.splitMaskJointClosureRules Parts)
        ((splitMaskJointRootExpansion A.splitMaskHybrid).induce S) := by
  have hAmbient :
      IsUClosed (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion A.splitMaskHybrid) :=
    A.splitMaskJointRoot_isUClosed
  exact
    (nativeClosed_iff_jointHybridUSubstructure A hPos S).trans
      (hAmbient.induce_iff_USubstructure S).symm

end AllThoseRamseyClasses.Published
