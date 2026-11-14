import AllThoseRamseyClasses.Published.TrackEHybridOldDomainCoherence
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: complete original mask DOMAIN saturation

The original OLD complete-output-part mask language intentionally
contains a relation name for EVERY injective enumeration of a
finite set of output parts. A canonical genuine native
`toNonemptyPartial` source activates all those names when
their OUTPUT-PART SET equals the parts of its actual defined
nonempty F(xs) fibre.

The previously certified `SplitMaskHybridOriginalDomainCoherent`
law says only that TWO already-active masks have the same
output-part set. It does NOT require every mask name for that
same set to be active. An arbitrary noncanonical target might
activate a chosen mask ordering but omit its permutation. Its
OLD reduct would then fail to equal the complete-mask graph
of the decoded native function even if the function VALUE SET
and definedness were correctly reconstructed.

We explicitly isolate this independent necessary normalization:
once an ORIGINAL mask-domain relation is active for a
distinct input-root pattern, EVERY other complete mask with
the SAME SET of output parts is active on that identical root.

The law is true for canonical native sources. It is exact weak
hereditary: old domain predicates of the ambient target are
not recomputed from clipped output values. It is preserved by
genuine FULL base-hybrid relational free amalgamation: each
positive OLD domain tuple comes wholly from one side, and
saturation on that same side supplies the alternative mask.
No U-closedness, choice of decoder, new value or hull is used.

This is separate from cross-PATTERN domain transport, which is
already certified, and from complete output-tuple existence,
which requires positive-root JOINT U-closedness. It is NOT
a full re-encoding theorem or the two-pass sparse Ramsey step.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every alternate complete output-part mask enumerating
the SAME OUTPUT-PART SET is active whenever one original
mask-domain relation is active on that input root. The
two mask lists may differ in order, but the primitive
function symbol, root equality pattern and root tuple
stay literally the same. -/
def HybridOriginalMaskDomainSaturated
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (p : FunctionInputPattern L)
    (maskA maskB : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V),
    E.rel (hybridOriginalMaskDomainSymbol p maskA) root →
    Set.range maskA.label = Set.range maskB.label →
    E.rel (hybridOriginalMaskDomainSymbol p maskB) root

/-- The same part set provides an IFF between original
mask-domain predicates, not just the forward saturation. -/
theorem HybridOriginalMaskDomainSaturated.domain_iff_of_sameParts
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridOriginalMaskDomainSaturated E)
    (p : FunctionInputPattern L)
    (maskA maskB : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V)
    (hParts : Set.range maskA.label = Set.range maskB.label) :
    E.rel (hybridOriginalMaskDomainSymbol p maskA) root ↔
      E.rel (hybridOriginalMaskDomainSymbol p maskB) root :=
  ⟨fun hA => h p maskA maskB root hA hParts,
   fun hB => h p maskB maskA root hB hParts.symm⟩

/-- Every genuine native source `System.splitMaskHybrid` has
literal saturation: its ORIGINAL OLD domain relation depends
on the COMPLETE SET of output PARTS of the genuine fibre,
not on which injective mask list enumerates that set. -/
theorem canonicalHybrid_originalMaskDomainSaturated
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridOriginalMaskDomainSaturated A.splitMaskHybrid := by
  classical
  intro p maskA maskB root hActive hSameParts
  have hRaw :
      Function.Injective root ∧
      ∃ U : Set V,
        A.toStructure.toNonemptyPartial.func
          p.symbol (root ∘ p.argMap) = some U ∧
        A.part '' U = Set.range maskA.label := by
    exact hActive
  obtain ⟨hInj, U, hSome, hParts⟩ := hRaw
  change Function.Injective root ∧
    ∃ U : Set V,
      A.toStructure.toNonemptyPartial.func
        p.symbol (root ∘ p.argMap) = some U ∧
      A.part '' U = Set.range maskB.label
  exact ⟨hInj, U, hSome, hParts.trans hSameParts⟩

/-- Literal induced vertex sets preserve saturation of all
original domain-mask predicate names, even when whole
output tuples leave the weak set. -/
theorem HybridOriginalMaskDomainSaturated.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridOriginalMaskDomainSaturated E)
    (S : Set V) :
    HybridOriginalMaskDomainSaturated (E.induce S) := by
  intro p maskA maskB root hActive hSameParts
  exact h p maskA maskB (Subtype.val ∘ root) hActive hSameParts

/-- A TRUE FULL relational free amalgam cannot create a
counterexample to original mask saturation when both
side Pictures are saturated: a positive original domain
tuple comes from one side, and the alternate mask
relation from that side maps through the SAME embedding. -/
theorem HybridOriginalMaskDomainSaturated.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridOriginalMaskDomainSaturated Left)
    (hRight : HybridOriginalMaskDomainSaturated Right) :
    HybridOriginalMaskDomainSaturated Whole := by
  intro p maskA maskB root hActive hSameParts
  rcases (hFree.rel_iff
      (hybridOriginalMaskDomainSymbol p maskA) root).mp
      hActive with
    ⟨x, hx, hRoot⟩ | ⟨y, hy, hRoot⟩
  · have hOther : Left.rel
        (hybridOriginalMaskDomainSymbol p maskB) x :=
      hLeft p maskA maskB x hx hSameParts
    have hWhole : Whole.rel
        (hybridOriginalMaskDomainSymbol p maskB) (iL ∘ x) :=
      (iL.map_rel_iff (hybridOriginalMaskDomainSymbol p maskB) x).mpr
        hOther
    exact (congrArg (fun t : Fin p.rootSize → C =>
      Whole.rel (hybridOriginalMaskDomainSymbol p maskB) t)
      hRoot).mpr hWhole
  · have hOther : Right.rel
        (hybridOriginalMaskDomainSymbol p maskB) y :=
      hRight p maskA maskB y hy hSameParts
    have hWhole : Whole.rel
        (hybridOriginalMaskDomainSymbol p maskB) (iR ∘ y) :=
      (iR.map_rel_iff (hybridOriginalMaskDomainSymbol p maskB) y).mpr
        hOther
    exact (congrArg (fun t : Fin p.rootSize → C =>
      Whole.rel (hybridOriginalMaskDomainSymbol p maskB) t)
      hRoot).mpr hWhole

end StructuralRamsey.RelStructure
