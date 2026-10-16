import AllThoseRamseyClasses.Lifts.CommonGlobalCanonicalLift
import AllThoseRamseyClasses.Lifts.GlobalSharedPieceFlip

/-!
# Geometric forbidden-piece flips from a common FULL canonical lift

This combines the two independently kernel-checked Section 3
ingredients:

* `CommonGlobalCanonicalLift.agreeOn`: one common, fully induced
  global lifted substructure forces agreement of ALL added piece
  relations in the two canonical witness lifts;
* `geometricGlobalSharedLiftFlip`: agreement of the true global
  piece relation, together with an injective rooted weak piece
  realization, constructs a literal forbidden replacement source
  and a weak target map unchanged on its entire complement.

Unlike the intermediate lemma, the theorem below does NOT assume
agreement of new relation symbols as an independent oracle. It is
derived from the concrete common full lift and its TWO genuine full
expanded embeddings.

This is the actual common-witness flip mechanism of the 2019 paper,
with its remaining assumptions kept visible: the original forbidden
root has an injective image, the weak map of the chosen piece into
the left witness is provided, and both ambient witness embeddings
agree on the common carrier. None follows automatically from
arbitrary old-language embeddings or an arbitrary weak map.

We do NOT claim the complete unrestricted printed flip without
checking how the paper's maximal witness definition supplies this
common full lifted substructure, and how the forbidden-image closure
hypothesis supplies injectivity before the minimal-support proof.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The original geometric piece maps weakly into the left witness.
A common FULL global lift transfers its canonical class relation
to the right witness, where a genuine equivalent replacement piece
can be realized and flipped into the original forbidden source.

The result is a literal member of the forbidden family, complete
functional free-amalgam source embeddings, and a weak target map
which is EXACTLY the original map on the entire complement. -/
theorem geometricGlobalCommonFullLiftFlip
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
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
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
  exact geometricGlobalSharedLiftFlip F Forbidden
    hFinite hForbidden d hn Target f hf
    Left Right jLeft jRight X iLeft iRight
    (hCommon.agreeOn F) hTargetAgree
    pLeft hpLeft hPieceMap xsX hRootLeft hRootImageInjective

/-- The common lift also transports the TRUE globally indexed
canonical relation for a single selected piece, without assuming
that the whole forbidden structure maps into the left witness. -/
theorem geometricGlobalRelation_from_common_lift_piece
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V UX UA UB : Type}
    (Forbidden : Structure L V)
    (hFinite : Finite V) (hForbidden : F Forbidden)
    (d : GeometricFunctionalPieceData Forbidden n) (hn : 0 < n)
    (Left : Structure L UA) (Right : Structure L UB)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
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
  exact geometricGlobalRelation_shared_from_piece
    F Forbidden hFinite hForbidden d hn
    Left Right X iLeft iRight (hCommon.agreeOn F)
    pLeft hpLeft xsX hRootLeft hRootInj

end AllThoseRamseyClasses.Lifts
