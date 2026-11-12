import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam

/-!
# Track E2: OLD output-part masks determine split domains

The hybrid source has original complete output-part mask domains
and one split singleton function domain for each part q. Whenever
a genuine OLD original mask m is active on a distinct input root,
the split domain at q is active precisely when q is among m's labels.

We name this pointwise law for arbitrary hybrid pictures, establish
it for actual native canonical hybrid Systems and show that it
persists on every EXACT induced weak subset. No outputs are
recomputed after clipping, and no closure hull is inserted.

The assertion does not guarantee existence of an original mask
for every split active domain in an arbitrary hybrid target.
Other target coherence/decoding and the E2 sparse construction
remain separate.
-/

namespace StructuralRamsey.Language

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Split input pattern indexed by part q, with the same original
distinct-root equality pattern and repeated input coordinates. -/
def splitMaskInputAtPart
    (p : FunctionInputPattern L) (q : Parts) :
    FunctionInputPattern (L.outputPartIndexed Parts) where
  symbol := (ULift.up p.symbol, q)
  rootSize := p.rootSize
  argMap := p.argMap
  onto := p.onto

end StructuralRamsey.Language

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- An original complete-output active mask exactly describes
the collection of active singleton split output-part domains. -/
def HybridMaskSplitDomainCompatible
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (m : Language.CompleteOutputParts Parts)
    (q : Parts) (root : Fin p.rootSize → V),
    E.rel (Language.hybridOriginalMaskDomainSymbol p m) root →
    (E.rel
      (Language.hybridSplitDomainSymbol
        (Language.splitMaskInputAtPart p q)) root ↔
      q ∈ Set.range m.label)

/-- Every genuine native canonical hybrid System satisfies the
original mask/split-domain compatibility, including repeated
primitive inputs and non-singleton original fibres. -/
theorem canonicalHybrid_maskSplitDomainCompatible
    {V : Type w}
    (A : StructuralRamsey.FunctionalPartite.System L Parts V) :
    HybridMaskSplitDomainCompatible A.splitMaskHybrid := by
  classical
  intro p m q root hMask
  let T : Set V := A.func p.symbol (root ∘ p.argMap)
  have hOld :
      Function.Injective root ∧
      ∃ U : Set V,
        A.toStructure.toNonemptyPartial.func
          p.symbol (root ∘ p.argMap) = some U ∧
        A.part '' U = Set.range m.label := by
    exact hMask
  obtain ⟨hRootInj, U, hValue, hPartMask⟩ := hOld
  have hDefined : T.Nonempty := by
    by_contra hn
    have hNone :
        A.toStructure.toNonemptyPartial.func
          p.symbol (root ∘ p.argMap) = none := by
      change (if T.Nonempty then some T else none) = none
      simp [hn]
    rw [hNone] at hValue
    cases hValue
  have hU : U = T := by
    change (if T.Nonempty then some T else none) = some U at hValue
    simpa only [if_pos hDefined, Option.some.injEq] using hValue.symm
  rw [hU] at hPartMask
  change (Function.Injective root ∧
      ({y : V | y ∈ T ∧ A.part y = q}).Nonempty) ↔
      q ∈ Set.range m.label
  constructor
  · rintro ⟨_, y, hy⟩
    have hImage : q ∈ A.part '' T :=
      ⟨y, hy.1, hy.2⟩
    rw [hPartMask] at hImage
    exact hImage
  · intro hq
    rw [← hPartMask] at hq
    obtain ⟨y, hy, hpart⟩ := hq
    exact ⟨hRootInj, y, ⟨hy, hpart⟩⟩

/-- The law passes to exact weak induced vertex subsets, even if
the corresponding original output tuple leaves the weak set. -/
theorem HybridMaskSplitDomainCompatible.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridMaskSplitDomainCompatible E)
    (S : Set V) :
    HybridMaskSplitDomainCompatible (E.induce S) := by
  intro p m q root hMask
  exact h p m q (Subtype.val ∘ root) hMask

end StructuralRamsey.RelStructure
