import AllThoseRamseyClasses.Lifts.FullComplementClosedOuterRoot
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Track C: arbitrary closed contextual roots factor through the unchanged inner complement

The generic all-test contextual congruence is formulated for ANY
fully embedded outer root in the closed retained complement E|SR
of an actual inner source decomposition. The older theorem
factoring through that complement was available only for the
ordered root of a genuine outer geometric minimal-separator piece.

Nothing in the factorization argument requires geometric
minimality of the OUTER context. Let K be ANY function-closed
set of the original native functional source Old and let
RootOuter be ANY complete FULL rooted substructure of Old
whose image lies in K and avoids the selected inner geometric
piece d's nonroot component D. Then the entire RootOuter
factors through the old full complement E = Old minus D
and through the exact closed retained subset SR=E∩K:

  RootOuter → E|SR → E → Old,

preserving every source vertex coordinate ON THE NOSE.

In particular if the whole RootOuter lies in the shared target
root preimage S and the inner piece's selected component is
B-only (hence outside S), the factorization is automatic.
No intermediate A-support minimality, nonnative weak-image
quotient or global injectivity of the EHN target map enters.

This removes the geometricity of K from the outer-root-chart
prerequisite of the generic closed-context all-test profile
congruence and the alternative no-escape iteration.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A full outer root embedded in an arbitrary closed contextual
carrier K and disjoint from the selected inner component D
factors as a genuine FULL functional root embedding into
E|SR, where SR is the exact preimage of K under the full
inner-complement embedding E → Old.

The returned coordinates are literally those of the original
outer root. K need not be a minimal closed separator. -/
theorem closedContextRoot_factorsFully_into_innerComplement
    {V R : Type}
    (Old : Structure L V)
    {m : ℕ} (d : GeometricFunctionalPieceData Old m)
    (K : Set V) (hKclosed : Old.IsClosed K)
    (RootOuter : Structure L R)
    (rootOld : Structure.Embedding RootOuter Old)
    (hRootInK : ∀ r : R, rootOld r ∈ K)
    (hRootOutsideInner : ∀ r : R,
      rootOld r ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left) :
    let E := geometricGlobalComplementChart Old d
    let iOldE : Structure.Embedding E.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    let SR : Set E.Carrier := iOldE ⁻¹' K
    let hSR : E.str.IsClosed SR :=
      functionalEmbedding_preimage_closed
        E.str Old iOldE K hKclosed
    ∃ rE : Structure.Embedding RootOuter (E.str.induce SR hSR),
      ∀ r : R, (rE r).1.1 = rootOld r := by
  classical
  let E := geometricGlobalComplementChart Old d
  let iOldE : Structure.Embedding E.str Old :=
    functionalComponentComplementEmbedding Old
      (Set.range d.roots) d.minimal.1 d.left
  let SR : Set E.Carrier := iOldE ⁻¹' K
  have hSR : E.str.IsClosed SR :=
    functionalEmbedding_preimage_closed
      E.str Old iOldE K hKclosed
  let f : R → E.Carrier :=
    fun r => ⟨rootOld r, hRootOutsideInner r⟩
  have hf (r : R) : rootOld r = iOldE (f r) := rfl
  let rootToE : Structure.Embedding RootOuter E.str :=
    rootOld.factorWithMap iOldE f hf
  have hRootVal (r : R) : (rootToE r).1 = rootOld r := by
    rfl
  have hRetained (r : R) : rootToE r ∈ SR := by
    change (rootToE r).1 ∈ K
    rw [hRootVal]
    exact hRootInK r
  let incSR : Structure.Embedding
      (E.str.induce SR hSR) E.str :=
    Structure.inclusion E.str SR hSR
  let g : R → SR := fun r => ⟨rootToE r, hRetained r⟩
  have hg (r : R) : rootToE r = incSR (g r) := rfl
  let rE : Structure.Embedding RootOuter
      (E.str.induce SR hSR) :=
    rootToE.factorWithMap incSR g hg
  refine ⟨rE, ?_⟩
  intro r
  exact hRootVal r

/-- No need to postulate avoidance of the inner component if
the entire contextual outer root lies in a full seam S and
the actual selected inner component is disjoint from S.

This is the source-geometric situation after a B-only
component is chosen from the native full target amalgam. -/
theorem closedContextRoot_factorsFully_of_seamDisjointInner
    {V R : Type}
    (Old : Structure L V)
    {m : ℕ} (d : GeometricFunctionalPieceData Old m)
    (K : Set V) (hKclosed : Old.IsClosed K)
    (RootOuter : Structure L R)
    (rootOld : Structure.Embedding RootOuter Old)
    (hRootInK : ∀ r : R, rootOld r ∈ K)
    (S : Set V)
    (hOuterRootInS : ∀ r : R, rootOld r ∈ S)
    (hInnerComponentOutsideS :
      ∀ z : V,
        z ∈ functionalComponentFrom Old
          (Set.range d.roots) d.left → z ∉ S) :
    let E := geometricGlobalComplementChart Old d
    let iOldE : Structure.Embedding E.str Old :=
      functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left
    let SR : Set E.Carrier := iOldE ⁻¹' K
    let hSR : E.str.IsClosed SR :=
      functionalEmbedding_preimage_closed
        E.str Old iOldE K hKclosed
    ∃ rE : Structure.Embedding RootOuter (E.str.induce SR hSR),
      ∀ r : R, (rE r).1.1 = rootOld r := by
  have hRootOutsideInner : ∀ r : R,
      rootOld r ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left := by
    intro r hr
    exact hInnerComponentOutsideS (rootOld r) hr
      (hOuterRootInS r)
  exact closedContextRoot_factorsFully_into_innerComplement
    Old d K hKclosed RootOuter rootOld
    hRootInK hRootOutsideInner

end AllThoseRamseyClasses.Lifts
