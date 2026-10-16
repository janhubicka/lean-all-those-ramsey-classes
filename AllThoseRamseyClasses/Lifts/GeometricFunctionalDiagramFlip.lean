import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# A flip directly from an actual geometric functional forbidden source

Using the now verified exact root chart, a forbidden source A and
closed Gaifman separator R decompose into the selected piece and its
closed complement. Assume an equivalent replacement root extension
P' has a weak 2019 homomorphism-embedding into the desired target
which agrees with the original weak map on the root. The fixed-root
source diagram flip gives a NEW forbidden source and a weak map that
agrees with the replacement piece map and the original map on the
unchanged complement.

This eliminates the previously open geometric-to-fixed-root diagram
normalization. The next semantic step is replacing the diagram
equivalence hypothesis by the published canonical piece equivalence;
the independently audited canonical-glue equivalence bridge is
intended to discharge that obligation. Existence of P' from the
canonical lift and the final minimal-subpiece induction are still
separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V UT : Type v}

/-- A geometric forbidden-source flip, keeping the complement's
original map EXACTLY on its vertices. The resulting source is a
genuine member of the forbidden family with an actual full
free-amalgam certificate. -/
theorem geometricFunctionalDiagramFlip
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R)
    (root : {v : V // v ∉ R})
    (Forbidden : ∀ {W : Type v}, Structure L W → Prop)
    (hForbidden : Forbidden A)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (P' : FunctionalRootExtension (closedCutRoot A R hR))
    (hEq : (functionalDiagramPieceSetoid
      (closedCutRoot A R hR) Forbidden).r
      (componentPieceRootExtension A R hR root) P')
    (pP' : P'.Carrier → UT)
    (hpP' : P'.str.IsEHNHomomorphismEmbedding Target pP')
    (hRoot : ∀ r : R,
      pP' (P'.rootEmbedding r) = f r.1) :
    ∃ (W : Type v) (Source : Structure L W),
      Forbidden Source ∧
      ∃ (iP : Structure.Embedding P'.str Source)
        (iQ : Structure.Embedding
          (componentComplementRootExtension A R hR root).str Source),
        Structure.IsFreeAmalgam
          P'.rootEmbedding
          (componentComplementRootExtension A R hR root).rootEmbedding
          iP iQ ∧
        ∃ flip : W → UT,
          Source.IsEHNHomomorphismEmbedding Target flip ∧
          (∀ a : P'.Carrier, flip (iP a) = pP' a) ∧
          ∀ b : (componentComplementRootExtension A R hR root).Carrier,
            flip (iQ b) = f b.1 := by
  let Q : FunctionalRootExtension (closedCutRoot A R hR) :=
    componentComplementRootExtension A R hR root
  let pQ : Q.Carrier → UT := fun b => f b.1
  have hpQ : Q.str.IsEHNHomomorphismEmbedding Target pQ := by
    exact hf.comp
      (functionalComponentComplementEmbedding A R hR root).isEHNHomomorphismEmbedding
  have hcompat : ∀ r : R,
      pP' (P'.rootEmbedding r) = pQ (Q.rootEmbedding r) := by
    intro r
    change pP' (P'.rootEmbedding r) = f r.1
    exact hRoot r
  have hOld : forbiddenFunctionalDiagram
      (closedCutRoot A R hR) Forbidden
      (componentPieceRootExtension A R hR root) Q :=
    functionalSource_hasRootChartDiagram A R hR root
      Forbidden hForbidden
  exact functionalDiagramFlip (closedCutRoot A R hR)
    Forbidden (componentPieceRootExtension A R hR root)
    P' Q hEq hOld Target pP' pQ hcompat hpP' hpQ

/-- The actual MINIMAL closed separator case, which is the
geometric piece data selected in the paper. Unlike the general
closed-cut form, this theorem stores both distinct complementary
components and their minimality. -/
theorem geometricMinimalPieceDiagramFlip
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (Forbidden : ∀ {W : Type v}, Structure L W → Prop)
    (hForbidden : Forbidden A)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (P' : FunctionalRootExtension
      (closedCutRoot A (Set.range d.roots) d.minimal.1))
    (hEq : (functionalDiagramPieceSetoid
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
            flip (iQ b) = f b.1 :=
  geometricFunctionalDiagramFlip A (Set.range d.roots)
    d.minimal.1 d.left Forbidden hForbidden
    Target f hf P' hEq pP' hpP' hRoot

end AllThoseRamseyClasses.Lifts
