import AllThoseRamseyClasses.Lifts.CanonicalGlueDiagramBridge
import AllThoseRamseyClasses.Lifts.GeometricFunctionalDiagramFlip

/-!
# Canonical-equivalence flip for a geometric minimal-cut forbidden piece

The actual source form of the 2019 Section 3 flip now takes EXACTLY
the canonical free-gluing incompatibility equivalence at the induced
full root: it no longer assumes equality of a separately defined
existential-diagram profile.

The equivalence of those notions is kernel-proved in
`functionalDiagramPiece_equiv_iff_glue`; the actual-source flip
is kernel-proved in `geometricMinimalPieceDiagramFlip`.

Given a new equivalent rooted piece P' and a weak map into the target
matching the root, the result is a new literal forbidden source,
its FULL functional free-amalgam diagram, and a weak 2019-style map
which agrees with the original weak map on the entire complement.

The still-open manuscript ingredient is to obtain P' and its target
map from the common maximal CANONICAL LIFT relation and to normalize
arbitrary root tuples to these fixed full functional root charts.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V UT : Type v}

/-- The canonical-profile version of a flip of a genuine minimal
closed-separator piece of a forbidden structure. This theorem
discharges the full functional source and map portions of the
published flip, conditionally on the canonical-lift witness P'. -/
theorem geometricMinimalPieceCanonicalFlip
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (Forbidden : ∀ {W : Type v}, Structure L W → Prop)
    (hForbidden : Forbidden A)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (P' : FunctionalRootExtension
      (closedCutRoot A (Set.range d.roots) d.minimal.1))
    (hEq : (functionalRootPieceSetoid
      (closedCutRoot A (Set.range d.roots) d.minimal.1)
      Forbidden).r
      (componentPieceRootExtension A (Set.range d.roots)
        d.minimal.1 d.left) P')
    (pP' : P'.Carrier → UT)
    (hpP' : P'.str.IsEHNHomomorphismEmbedding Target pP')
    (hRoot : ∀ r : Set.range d.roots,
      pP' (P'.rootEmbedding r) = f r.1) :
    ∃ (W : Type v) (Source : Structure L W),
      Forbidden Source ∧
      ∃ (iP : Structure.Embedding P'.str Source)
        (iQ : Structure.Embedding
          (componentComplementRootExtension A (Set.range d.roots)
            d.minimal.1 d.left).str Source),
        Structure.IsFreeAmalgam
          P'.rootEmbedding
          (componentComplementRootExtension A (Set.range d.roots)
            d.minimal.1 d.left).rootEmbedding
          iP iQ ∧
        ∃ flip : W → UT,
          Source.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ a : P'.Carrier, flip (iP a) = pP' a) ∧
          ∀ b : (componentComplementRootExtension A (Set.range d.roots)
              d.minimal.1 d.left).Carrier,
            flip (iQ b) = f b.1 := by
  have hEqDiagram :
      (functionalDiagramPieceSetoid
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        Forbidden).r
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left) P' :=
    (functionalDiagramPiece_equiv_iff_glue
      (closedCutRoot A (Set.range d.roots) d.minimal.1)
      Forbidden
      (componentPieceRootExtension A (Set.range d.roots)
        d.minimal.1 d.left) P').mpr hEq
  exact geometricMinimalPieceDiagramFlip
    A d Forbidden hForbidden Target f hf
    P' hEqDiagram pP' hpP' hRoot

end AllThoseRamseyClasses.Lifts
