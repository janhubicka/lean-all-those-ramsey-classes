import AllThoseRamseyClasses.Published.TrackEHybridSplitPositiveNativeSound
import AllThoseRamseyClasses.Published.TrackEHybridNativeToSplitPositive
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: exact positive split graph of the decoded native function

The two independent Track E2 implications fit together with
no extra generated vertices, output completion or change to the
selected target carrier:

* Positive split incidence -> a complete ORIGINAL OLD tuple
  already present in the ACTUAL JOINT-U-closed strict-normal
  target -> membership in the OLD decoded native function fibre.
* Membership in the OLD decoded native function fibre, with
  the displayed output's unique unary part label -> a positive
  singleton split incidence on ANY injective distinct-input
  enumeration of the SAME primitive function input.

This module packages both as an actual IFF of the POSITIVE
split (F,q) graph and the decoded native positive fibre relation,
with the same input vertices and SAME output vertex y.

The proof is conditional on the exact joint U-closed target,
strict no-defined-empty hybrid normality, positive original
primitive function arity, positive split input-pattern transport,
injectivity of the displayed distinct-input root, and the
literal output unary part label. Those conditions are not
silently asserted for arbitrary weak sparse Pictures.

A separate step is needed for exact active SPLIT-domain relation
definedness and for exact re-encoding of the nested OLD/SPLIT
root tags. This is not the missing two-pass finite-family
ordered sparse Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The POSITIVE singleton split function graph of an actual
joint-U-closed native-decoder-normal hybrid target is exactly
the graph of the SAME ORIGINAL OLD decoded native function,
on the SAME primitive input and SAME output vertex y, once
the root is an injective distinct-input pattern and y has
the designated unary output-part label q.

No new target vertex or alternate decoder is introduced.
The equivalence does not assert an equivalence of the
separate split DOMAIN predicates for arbitrary weak tests. -/
theorem HybridJointNoEmptyNormal.splitOutput_iff_oldDecodedNative_mem
    {V : Type w}
    {C : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    (hNorm : HybridJointNoEmptyNormal C)
    (hClosed : IsUClosed (L.splitMaskJointClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hTransport : HybridSplitOutputPatternTransport
      (splitMaskJointRootReduct C))
    (p : FunctionInputPattern L)
    (root : Fin p.rootSize → V)
    (hRootInj : Function.Injective root)
    (q : Parts) (y : V)
    (hPart : (splitMaskJointRootReduct C).rel
      (.inr (.inr q)) (fun _ : Fin 1 => y)) :
    (splitMaskJointRootReduct C).rel
      (hybridSplitOutputSymbol (splitMaskInputAtPart p q))
        (Structure.funcTuple root y) ↔
    y ∈
      (((splitMaskHybridOriginalOldReduct
        (splitMaskJointRootReduct C)).wholeMaskPartialDecode).collapseDomain).func
        p.symbol (root ∘ p.argMap) := by
  constructor
  · intro hSplit
    have hMem :=
      hNorm.splitOutput_mem_oldDecodedNative
        hClosed hPos hTransport p q
        (Structure.funcTuple root y) hSplit
    simpa only [Structure.funcTuple_last,
      Structure.funcTuple_castSucc] using hMem
  · intro hMem
    exact hNorm.oldDecodedNative_mem_to_splitOutput
      hTransport p root hRootInj q y hPart hMem

end StructuralRamsey.RelStructure
