import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules
import PartiteConstruction.Functional.NativeWholeWeakFreeAmalgam
import PartiteConstruction.Structure.PartialSetFunctionsWholePartRepresent

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

/-- Conversely, in a FINITE canonical native partite System every
active singleton split (F,q)-domain comes from a genuine ORIGINAL
nonempty multivalued fibre. Transversality and the verified complete
output-part enumeration yield one active original OLD mask whose set
of output parts contains q.

The finite carrier assumption is used only to invoke the checked
complete-output representation lemma, not to enlarge any tested set.
This is SOURCE coverage, not a claim that an arbitrary hybrid target
has an original mask for each split domain. -/
theorem canonicalHybrid_activeSplitDomain_hasOriginalMask
    {V : Type w} [Finite V]
    (A : StructuralRamsey.FunctionalPartite.System L Parts V)
    (p : Language.FunctionInputPattern L)
    (q : Parts) (root : Fin p.rootSize → V)
    (hSplit : A.splitMaskHybrid.rel
      (Language.hybridSplitDomainSymbol
        (Language.splitMaskInputAtPart p q)) root) :
    ∃ m : Language.CompleteOutputParts Parts,
      A.splitMaskHybrid.rel
        (Language.hybridOriginalMaskDomainSymbol p m) root ∧
      q ∈ Set.range m.label := by
  classical
  let xs : Fin (L.funcArity p.symbol) → V := root ∘ p.argMap
  change Function.Injective root ∧
    ((A.splitOutputParts).toStructure.func
      (ULift.up p.symbol, q) xs).Nonempty at hSplit
  obtain ⟨hInj, y, hySplit⟩ := hSplit
  have hy : y ∈ A.func p.symbol xs ∧ A.part y = q := hySplit
  have hNonempty : (A.func p.symbol xs).Nonempty := ⟨y, hy.1⟩
  have hVal : A.toStructure.toNonemptyPartial.func p.symbol xs =
      some (A.func p.symbol xs) := by
    change (if (A.func p.symbol xs).Nonempty then
      some (A.func p.symbol xs) else none) = some (A.func p.symbol xs)
    simp only [if_pos hNonempty]
  have hTrans :
      StructuralRamsey.PartialSetStructure.FibreTransversal
        A.toStructure.toNonemptyPartial A.part := by
    intro F args U hF a ha b hb hab
    have hNative : A.func F args = U := by
      change (if (A.func F args).Nonempty then
        some (A.func F args) else none) = some U at hF
      by_cases hn : (A.func F args).Nonempty
      · simp only [if_pos hn] at hF
        exact Option.some.inj hF
      · simp only [if_neg hn] at hF
        cases hF
    rw [← hNative] at ha hb
    exact A.funcTransversal F args a b ha hb hab
  obtain ⟨m, ys, hRange, hLabels⟩ :=
    A.toStructure.toNonemptyPartial.completeOutputPartGraph_represents_value
      A.part hTrans p.symbol xs (A.func p.symbol xs) hVal
  have hParts : A.part '' (A.func p.symbol xs) =
      Set.range m.label := by
    rw [← hRange]
    ext part
    constructor
    · rintro ⟨z, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hLabels j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨ys j, ⟨j, rfl⟩, hLabels j⟩
  have hMask : A.splitMaskHybrid.rel
      (Language.hybridOriginalMaskDomainSymbol p m) root := by
    change Function.Injective root ∧
      ∃ U : Set V,
        A.toStructure.toNonemptyPartial.func p.symbol xs = some U ∧
        A.part '' U = Set.range m.label
    exact ⟨hInj, A.func p.symbol xs, hVal, hParts⟩
  refine ⟨m, hMask, ?_⟩
  rw [← hParts]
  exact ⟨y, hy.1, hy.2⟩

/-- Every active split primitive input domain has an actual
complete ORIGINAL OLD output mask whose parts contain the split
output-part label. This is the necessary reverse existence law,
not implied by the forward mask-to-split compatibility alone. -/
def HybridSplitDomainMaskCovered
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (p : Language.FunctionInputPattern L)
    (q : Parts) (root : Fin p.rootSize → V),
    E.rel (Language.hybridSplitDomainSymbol
      (Language.splitMaskInputAtPart p q)) root →
    ∃ m : Language.CompleteOutputParts Parts,
      E.rel (Language.hybridOriginalMaskDomainSymbol p m) root ∧
      q ∈ Set.range m.label

/-- In a finite genuine partite System, the checked complete
output-part tuple enumeration supplies the required original mask
for every active split-domain predicate. -/
theorem canonicalHybrid_splitDomainMaskCovered
    {V : Type w} [Finite V]
    (A : StructuralRamsey.FunctionalPartite.System L Parts V) :
    HybridSplitDomainMaskCovered A.splitMaskHybrid := by
  intro p q root hSplit
  exact canonicalHybrid_activeSplitDomain_hasOriginalMask A p q root hSplit

/-- The original active domain mask remains present under exact
induced WEAK restriction, even if all of its output vertices lie
outside the selected set. No function is recomputed. -/
theorem HybridSplitDomainMaskCovered.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridSplitDomainMaskCovered E)
    (S : Set V) :
    HybridSplitDomainMaskCovered (E.induce S) := by
  intro p q root hSplit
  exact h p q (Subtype.val ∘ root) hSplit

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


namespace StructuralRamsey.RelStructure.IsFreeAmalgam

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {H E F C : Type w}

/-- Exact original-mask/split-domain compatibility survives free
amalgamation of FULL hybrid relational embeddings. Once the original
active mask is localized on a side, the full side embedding reflects
the corresponding singleton split-domain relation on that SAME root.
No additional mixed-root, closedness or uniqueness hypothesis. -/
theorem hybridMaskSplitDomainCompatible
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridMaskSplitDomainCompatible Left)
    (hRight : HybridMaskSplitDomainCompatible Right) :
    HybridMaskSplitDomainCompatible Whole := by
  intro p m q root hMask
  let splitSymbol : (L.splitMaskHybrid Parts).Symbol :=
    Language.hybridSplitDomainSymbol
      (Language.splitMaskInputAtPart p q)
  rcases (hFree.rel_iff
      (Language.hybridOriginalMaskDomainSymbol p m) root).mp hMask with
    ⟨xs, hxs, hEq⟩ | ⟨xs, hxs, hEq⟩
  · have hTransport : Whole.rel splitSymbol root ↔
        Left.rel splitSymbol xs := by
      rw [hEq]
      exact iL.map_rel_iff splitSymbol xs
    exact hTransport.trans (hLeft p m q xs hxs)
  · have hTransport : Whole.rel splitSymbol root ↔
        Right.rel splitSymbol xs := by
      rw [hEq]
      exact iR.map_rel_iff splitSymbol xs
    exact hTransport.trans (hRight p m q xs hxs)

end StructuralRamsey.RelStructure.IsFreeAmalgam
