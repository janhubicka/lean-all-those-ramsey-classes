import AllThoseRamseyClasses.Lifts.GlobalSharedPieceFlip
import AllThoseRamseyClasses.Lifts.SelectedGlobalFlipGeometricWitness

/-!
# Same genuine selected Q from the COMMON full global canonical lift

Strengthen the verified common global full source flip by retaining the
geometric-selection certificate of its ACTUAL replacement Q.

A mere equality of full-rooted incompatibility profiles does not prove
that Q has one connected private component. The global relation witness
does supply a genuinely selected geometric Q, and the existing exact
selected source flip already constructs the literal source from that Q.
This theorem retains the certificate while preserving the SAME Q,
new full source, all full native function fibres, and complement map.

This is a source interface, not a claim of terminating Claim 2 support
descent or weak target-root injectivity. Full CI and #print axioms
are required before validation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- Genuine geometric selection and complete source diagram for the
SAME new Q obtained by flipping across a common FULL global lift. -/
theorem geometricGlobalSharedLiftFlip_selected
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB UT : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : Forbidden.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iLeft iRight)
    (hTargetAgree : ∀ x : UX,
      jLeft (iLeft x) = jRight (iRight x))
    (pLeft : (geometricGlobalFunctionalChart Forbidden d).ext.Carrier → UA)
    (hpLeft : Structure.IsEHNHomomorphismEmbedding
      ((geometricGlobalFunctionalChart Forbidden d).ext.str)
      Left pLeft)
    (hPieceMap : ∀ z :
      (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
      jLeft (pLeft z) = f z.1)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft ((geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding i)
        = iLeft (xsX i))
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => f (d.roots i))) :
    let P := geometricGlobalSelectedChart F Forbidden
      hFinite hForbidden d
    let T := geometricGlobalComplementChart Forbidden d
    ∃ Q : FunctionalRootExtension P.1.root,
      (functionalRootPieceSetoid P.1.root F).r P.1.ext Q ∧
      (FunctionalRootExtension.toEnumeratedRootedPattern
        P.1.root (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n ∧
      ∃ g : Q.Carrier → UB,
        Q.str.IsEHNHomomorphismEmbedding Right g ∧
        (∀ i : Fin n, g (Q.rootEmbedding i) = iRight (xsX i)) ∧
        ∃ (W : Type) (Source : Structure L W),
          F Source ∧
          ∃ (iQ : Structure.Embedding Q.str Source)
            (iT : Structure.Embedding T.str Source),
            Structure.IsFreeAmalgam Q.rootEmbedding T.rootEmbedding
              iQ iT ∧
            ∃ flip : W → UT,
              Source.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iQ a) = jRight (g a)) ∧
              (∀ b : T.Carrier, flip (iT b) = f b.1) := by
  let P : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Forbidden hFinite hForbidden d
  let rootLeft := fun i : Fin n => P.1.ext.rootEmbedding i
  have hPieceRoot (i : Fin n) :
      jLeft (pLeft (rootLeft i)) = f (d.roots i) := by
    exact hPieceMap (rootLeft i)
  have hLeftRootInj :
      Function.Injective (fun i : Fin n => pLeft (rootLeft i)) := by
    intro i j hij
    apply hRootImageInjective
    calc
      f (d.roots i) = jLeft (pLeft (rootLeft i)) :=
        (hPieceRoot i).symm
      _ = jLeft (pLeft (rootLeft j)) := congrArg jLeft hij
      _ = f (d.roots j) := hPieceRoot j
  have hRelRight :
      (globalFunctionalCanonicalLift F Right).rel
        (.inr (geometricGlobalPieceSymbol
          F Forbidden hFinite hForbidden d hn))
        (iRight ∘ xsX) :=
    geometricGlobalRelation_shared_from_piece
      F Forbidden hFinite hForbidden d hn
      Left Right X iLeft iRight hAgree
      pLeft hpLeft xsX hRootLeft hLeftRootInj
  have hRightCoordinates :
      ∀ i : Fin n, jRight (iRight (xsX i)) =
        f (d.roots i) := by
    intro i
    calc
      jRight (iRight (xsX i)) = jLeft (iLeft (xsX i)) :=
        (hTargetAgree (xsX i)).symm
      _ = jLeft (pLeft (rootLeft i)) :=
        congrArg jLeft (hRootLeft i).symm
      _ = f (d.roots i) := hPieceRoot i
  let T := geometricGlobalComplementChart Forbidden d
  let pT : T.Carrier → UT := fun b => f b.1
  have hpT : T.str.IsEHNHomomorphismEmbedding Target pT :=
    hf.comp (functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left).isEHNHomomorphismEmbedding
  have hOldDiagram : forbiddenFunctionalDiagram
      P.1.root F P.1.ext T :=
    geometricGlobalSource_has_forbidden_diagram
      F Forbidden hFinite hForbidden d
  have hRightRoot (i : Fin n) :
      jRight ((iRight ∘ xsX) i) = pT (T.rootEmbedding i) := by
    change jRight (iRight (xsX i)) = f (d.roots i)
    exact hRightCoordinates i
  obtain ⟨Q, hEq, hSelected, g, hg, hCoords,
      W, Source, hF, iQ, iT, hFree, flip, hFlip,
      hQMap, hTMap⟩ :=
    selectedGlobalCanonicalDiagramFlip_geometricWitness
      F P hn T hOldDiagram
      Right Target jRight (iRight ∘ xsX)
      hRelRight pT hpT hRightRoot
  exact ⟨Q, hEq, hSelected, g, hg, hCoords,
    W, Source, hF, iQ, iT, hFree, flip, hFlip, hQMap, hTMap⟩

end AllThoseRamseyClasses.Lifts
