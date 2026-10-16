import AllThoseRamseyClasses.Lifts.GlobalCommonLiftAgreement
import AllThoseRamseyClasses.Lifts.GlobalGeometricCanonicalFlip

/-!
# Flip a geometric forbidden piece from the SHARED GLOBAL canonical lift

The original 2019 flip argument needs only a WEAK realization of
the selected piece in the left witness: the whole forbidden source
need not map there, since its other components may lie on the right.

Suppose the genuine selected piece maps by a weak EHN map into Left,
with its ordered root image lying in the common substructure X.
The two global canonical lifts agree on X. If the original source's
weak map has an injective root image, its piece map realizes the
original GLOBAL class relation on Left and hence the same relation
on the corresponding tuple in Right.

The now verified global geometric source-flip theorem uses exactly
this Right relation to construct an ACTUAL forbidden replacement
source with a complete functional free-amalgam certificate and a
weak target map unchanged on the ENTIRE original complement.

The root-image injectivity and common-lift agreement remain explicit:
neither follows from an arbitrary weak map or a merely shared
old-language substructure. The final strong-amalgamation argument
must establish these through its injective forbidden-image reduction
and maximal-lift witness conditions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- Transfer the GLOBAL piece-class relation from a weak realization
of the selected GEOMETRIC PIECE in Left to Right through the common
fully induced lifted substructure X.

No weak realization of the whole forbidden source in Left is assumed.
This is the precise form used in the manuscript's flip proof. -/
theorem geometricGlobalRelation_shared_from_piece
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (Left : Structure L UA) (Right : Structure L UB)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hAgree : GlobalCanonicalLiftsAgreeOn F iLeft iRight)
    (pLeft : (geometricGlobalFunctionalChart Forbidden d).ext.Carrier → UA)
    (hpLeft : Structure.IsEHNHomomorphismEmbedding
      ((geometricGlobalFunctionalChart Forbidden d).ext.str)
      Left pLeft)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft ((geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding i)
        = iLeft (xsX i))
    (hRootInj : Function.Injective
      (fun i : Fin n =>
        pLeft ((geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding i))) :
    (globalFunctionalCanonicalLift F Right).rel
      (.inr (geometricGlobalPieceSymbol
        F Forbidden hFinite hForbidden d hn))
      (iRight ∘ xsX) := by
  let P : SelectedFunctionalChart F n :=
    geometricGlobalSelectedChart F Forbidden hFinite hForbidden d
  have hRelLeft :
      (globalFunctionalCanonicalLift F Left).rel
        (.inr (globalPieceSymbolOf F P hn))
        (fun i : Fin n => pLeft (P.1.ext.rootEmbedding i)) :=
    globalCanonicalRelation_of_selected_weak
      F P hn Left pLeft hpLeft hRootInj
  have hTuple :
      (fun i : Fin n => pLeft (P.1.ext.rootEmbedding i)) =
        (iLeft ∘ xsX) := by
    funext i
    exact hRootLeft i
  rw [hTuple] at hRelLeft
  have hRelRight :
      (globalFunctionalCanonicalLift F Right).rel
        (.inr (globalPieceSymbolOf F P hn))
        (iRight ∘ xsX) :=
    (hAgree (globalPieceSymbolOf F P hn) xsX).mp hRelLeft
  exact hRelRight

/-- A SHARED global canonical lift and a weak realization of a
geometric forbidden piece on its left side produce an ACTUAL
forbidden-source flip on the right. All new relation symbols used
here are the genuine quotient-indexed symbols of the global lift.

The output includes the selected equivalent replacement piece Q,
its weak realizing map g into Right, the literal new forbidden
source, its full functional free-amalgam diagram, and the flip map
which agrees with the old source map on every complement vertex. -/
theorem geometricGlobalSharedLiftFlip
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
  exact geometricGlobalCanonicalFlip_of_relation
    F Forbidden hFinite hForbidden d hn
    Target f hf Right jRight (iRight ∘ xsX)
    hRightCoordinates hRelRight

end AllThoseRamseyClasses.Lifts
