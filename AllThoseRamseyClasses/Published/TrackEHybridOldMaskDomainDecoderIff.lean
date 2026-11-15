import AllThoseRamseyClasses.Published.TrackEHybridOriginalMaskDomainSaturation
import AllThoseRamseyClasses.Published.TrackEHybridDecodedOldFibreTransversal
import AllThoseRamseyClasses.Published.TrackEJointOldDomainDecoderDefinedness
import AllThoseRamseyClasses.Published.TrackEHybridOldDecoderUnique

/-!
# Track E2: exact OLD complete-mask DOMAIN re-encoding for native decoders

The original hybrid OLD graph records separate domain predicates
for each full output-part MASK. Correctness of the chosen OLD
whole-mask decoder's value set and definedness does not alone
make those individual domain relations equal to the canonical
mask-domain relations of the decoded native Structure:
one mask may be active and another permutation of the same
output-part set absent in an arbitrary noncanonical Picture.

Here the now merged `HybridOriginalMaskDomainSaturated` property
supplies the missing mask-permutation direction, while the already
merged original-mask cross-pattern transport bridges different
injective presentations of the same primitive input F(xs).

Under literal joint-U-closedness, positive primitive function
arity, exact joint root tags, strict no-defined-empty normality,
the cross-pattern split-output law and mask-domain saturation,
we prove an IFF for the ORIGINAL OLD **domain relation** on
every input equality pattern and every complete output-part mask.
Its RHS is the native OLD decoder's actual defined value U and
the equality of its output-PART SET with the mask's part set,
together with input-root injectivity.

The proof uses exactly the already present output tuples and
vertices; it neither invents missing outputs nor constructs a
new target function. It is an intermediate re-encoding lemma,
not the full old output tuple/reflection theorem, inner tag
exactness, or the two-pass sparse ordered Ramsey witness.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- All parts of one visible complete ORIGINAL output tuple
are exactly the parts named by its mask, using the ACTUAL
unique unary part map of the hybrid Picture. In particular
there are no hidden output parts or unlabelled outputs. -/
theorem HybridPositiveOutputSound.wholeOutput_partSet_eq
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (hSound : HybridPositiveOutputSound E)
    (hUnique : HybridUniqueVertexPart E)
    (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (t : Fin (p.rootSize + mask.size) → V)
    (ht : E.rel (hybridOriginalMaskOutputSymbol p mask) t) :
    hUnique.partMap '' Set.range
        (fun j : Fin mask.size =>
          t (Fin.natAdd p.rootSize j)) =
      Set.range mask.label := by
  have hLabels (j : Fin mask.size) :
      hUnique.partMap (t (Fin.natAdd p.rootSize j)) =
        mask.label j := by
    exact hUnique.partMap_eq_of_label
      (t (Fin.natAdd p.rootSize j)) (mask.label j)
      (hSound.2.2.2 p mask j t ht)
  ext q
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, hy⟩
    exact ⟨j, (hLabels j).symm.trans hy⟩
  · rintro ⟨j, hj⟩
    exact ⟨t (Fin.natAdd p.rootSize j), ⟨j, rfl⟩,
      (hLabels j).trans hj⟩

/-- A particular OLD complete-mask DOMAIN predicate of an
actual noncanonical JOINT target equals the canonical domain
predicate computed from its EXISTING OLD native decoder.

The two directions are genuinely different:
* actual mask -> positive root closure creates an already
  present complete output tuple -> exact decoded value;
* decoded value with the specified output part set -> a
  visible OLD complete tuple on another equality pattern ->
  positive original domain soundness -> cross-pattern mask
  transport -> permutation saturation of all masks with
  the same output-part set.

This recovers individual ORIGINAL mask-domain predicates,
not just the existential domain bit. No generated hull or
new vertex is ever used. -/
theorem HybridJointNoEmptyNormal.originalMaskDomain_iff_oldDecoded
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hSplit : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (hSaturated : HybridOriginalMaskDomainSaturated
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (mask : CompleteOutputParts Parts)
    (root : Fin p.rootSize → V) :
    (splitMaskJointRootReduct C).rel
        (hybridOriginalMaskDomainSymbol p mask) root ↔
      Function.Injective root ∧
        ∃ U : Set V,
          ((splitMaskHybridOriginalOldReduct
            (splitMaskJointRootReduct C)).wholeMaskPartialDecode).func
              p.symbol (root ∘ p.argMap) = some U ∧
          (hNorm.normal.coherent.1.2.2.2.partMap) '' U =
            Set.range mask.label := by
  classical
  let Base : RelStructure (L.splitMaskHybrid Parts) V :=
    splitMaskJointRootReduct C
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) V :=
    splitMaskHybridOriginalOldReduct Base
  let part : V → Parts :=
    hNorm.normal.coherent.1.2.2.2.partMap
  constructor
  · intro hMask
    have hInj : Function.Injective root :=
      hNorm.normal.injectiveDomains.1 p mask root hMask
    have hRootPos : 0 < p.rootSize := by
      have hNe : p.rootSize ≠ 0 := by
        intro hz
        have i : Fin 0 :=
          hz ▸ p.argMap (⟨0, hPos p.symbol⟩ :
            Fin (L.funcArity p.symbol))
        exact i.elim0
      exact Nat.pos_of_ne_zero hNe
    obtain ⟨t, ⟨hOld, hPrefix⟩, _⟩ :=
      hNorm.originalMask_hasUniqueFullOutput
        hClosed p mask root hRootPos hMask
    let U : Set V := Set.range
      (fun j : Fin mask.size => t (Fin.natAdd p.rootSize j))
    have hHasValue :
        HasWholeMaskValue Old p.symbol
          (root ∘ p.argMap) U := by
      refine ⟨p.rootSize, p.argMap, p.onto, mask,
        t, hOld, ?_, rfl⟩
      intro i
      exact (hPrefix (p.argMap i)).symm
    have hDecoded :
        (Old.wholeMaskPartialDecode).func p.symbol
          (root ∘ p.argMap) = some U :=
      (hNorm.normal.coherent.oldDecoder_func_some_iff
        hNorm.normal.positive
        hNorm.normal.injectiveDomains
        hNorm.normal.originalMasks hSplit
        p.symbol (root ∘ p.argMap) U).mpr hHasValue
    have hPartSet :
        part '' U = Set.range mask.label :=
      hNorm.normal.positive.wholeOutput_partSet_eq
        hNorm.normal.coherent.1.2.2.2 p mask t hOld
    exact ⟨hInj, U, hDecoded, hPartSet⟩
  · rintro ⟨hInj, U, hDecoded, hPartSet⟩
    have hHasValue :
        HasWholeMaskValue Old p.symbol
          (root ∘ p.argMap) U :=
      (hNorm.normal.coherent.oldDecoder_func_some_iff
        hNorm.normal.positive
        hNorm.normal.injectiveDomains
        hNorm.normal.originalMasks hSplit
        p.symbol (root ∘ p.argMap) U).mp hDecoded
    obtain ⟨m, r, hr, maskB, t,
      hWhole, hArgs, hSet⟩ := hHasValue
    let patB : FunctionInputPattern L :=
      ⟨p.symbol, m, r, hr⟩
    let rootB : Fin m → V :=
      fun i => t (Fin.castAdd maskB.size i)
    have hOutputB :
        Base.rel (hybridOriginalMaskOutputSymbol patB maskB)
          t := hWhole
    have hDomB :
        Base.rel (hybridOriginalMaskDomainSymbol patB maskB)
          rootB :=
      hNorm.normal.positive.1 patB maskB t hOutputB
    have hArgsEq :
        rootB ∘ r = root ∘ p.argMap := by
      funext i
      exact (hArgs i).symm
    have hDomOnTarget :
        Base.rel (hybridOriginalMaskDomainSymbol p maskB)
          root :=
      hNorm.normal.originalMasks
        p.symbol m p.rootSize r p.argMap hr p.onto
        rootB root maskB hInj hArgsEq hDomB
    have hPartB :
        part '' Set.range
          (fun j : Fin maskB.size => t (Fin.natAdd m j)) =
            Set.range maskB.label :=
      hNorm.normal.positive.wholeOutput_partSet_eq
        hNorm.normal.coherent.1.2.2.2
        patB maskB t hOutputB
    have hMaskSet :
        Set.range maskB.label = Set.range mask.label := by
      calc
        Set.range maskB.label =
            part '' Set.range
              (fun j : Fin maskB.size => t (Fin.natAdd m j)) :=
          hPartB.symm
        _ = part '' U := by rw [hSet]
        _ = Set.range mask.label := hPartSet
    exact hSaturated p maskB mask root hDomOnTarget hMaskSet

end StructuralRamsey.RelStructure
