import AllThoseRamseyClasses.Lifts.GeometricCanonicalWitnessFlip

/-!
# The flip from a common canonical lifted relation in two witnesses

This is the paper's Section 3 flip proof scheme with its critical
root-image injectivity premise visible.

A forbidden source A has a genuine minimal closed separating piece
and a weak target map f. The entire induced piece has a weak map
into the LEFT ambient witness, agreeing with f after embedding the
left witness into the common target. If f is injective on the ordered
root tuple, this realizes the corresponding added canonical relation
in the left witness.

Assume that this added relation transports on the corresponding
ordered root tuple into the RIGHT witness. Its defining existential
predicate yields an equivalent replacement root extension and a
weak map into the right witness. We then invoke the previously
verified geometric canonical flip via the right-side embedding
to obtain a literal forbidden replacement source with its weak map
unchanged on the entire original complement.

This theorem deliberately does NOT infer root injectivity from a
general weak HE; the manuscript's tuple-surjective-image reduction
still needs to supply injectivity for its application.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {V UA UB UT : Type v}

/-- The common-lift flip statement, with the original piece
realized in the left witness and the canonical class relation
transported to the right witness. -/
theorem geometricMinimalPieceFlip_of_sharedCanonicalRelation
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (hFA : F A)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (Left : Structure L UA)
    (jLeft : Structure.Embedding Left Target)
    (pLeft : ↥(geometricPieceVertices A d) → UA)
    (hpLeft :
      (geometricFunctionalPiece A d).IsEHNHomomorphismEmbedding
        Left pLeft)
    (hPieceMap : ∀ z : ↥(geometricPieceVertices A d),
      jLeft (pLeft z) = f z.1)
    (hSourceRootInjective :
      Function.Injective (fun i : Fin n => f (d.roots i)))
    (Right : Structure L UB)
    (jRight : Structure.Embedding Right Target)
    (xsRight : Fin n → UB)
    (hRightRoot : ∀ i : Fin n,
      jRight (xsRight i) = f (d.roots i))
    (hSharedLift :
      (enumeratedRootClassCanonicalLift
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        (geometricCutRootEquiv A d)
        F
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left)
        Left).rel (.inr PUnit.unit)
          (fun i : Fin n =>
            pLeft
              ((componentPieceRootExtension A (Set.range d.roots)
                d.minimal.1 d.left).rootEmbedding
                (geometricCutRootEquiv A d i))) →
      (enumeratedRootClassCanonicalLift
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        (geometricCutRootEquiv A d)
        F
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left)
        Right).rel (.inr PUnit.unit) xsRight) :
    ∃ Q : FunctionalRootExtension
        (closedCutRoot A (Set.range d.roots) d.minimal.1),
      (functionalRootPieceSetoid
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        F).r
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left) Q ∧
      ∃ (g : Q.Carrier → UB),
        Q.str.IsEHNHomomorphismEmbedding Right g ∧
        (∀ i : Fin n,
          g (Q.rootEmbedding (geometricCutRootEquiv A d i)) =
            xsRight i) ∧
        ∃ (W : Type v) (Source : Structure L W),
          F Source ∧
          ∃ (iP : Structure.Embedding Q.str Source)
            (iC : Structure.Embedding
              (componentComplementRootExtension A
                (Set.range d.roots) d.minimal.1 d.left).str Source),
            Structure.IsFreeAmalgam Q.rootEmbedding
              (componentComplementRootExtension A
                (Set.range d.roots) d.minimal.1 d.left).rootEmbedding
              iP iC ∧
            ∃ flip : W → UT,
              Source.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier, flip (iP a) = jRight (g a)) ∧
              ∀ b : (componentComplementRootExtension A
                  (Set.range d.roots) d.minimal.1 d.left).Carrier,
                flip (iC b) = f b.1 := by
  let Root :=
    closedCutRoot A (Set.range d.roots) d.minimal.1
  let rho := geometricCutRootEquiv A d
  let P := componentPieceRootExtension A
    (Set.range d.roots) d.minimal.1 d.left
  have hPieceRoots (i : Fin n) :
      jLeft (pLeft (P.rootEmbedding (rho i))) =
        f (d.roots i) := by
    calc
      jLeft (pLeft (P.rootEmbedding (rho i))) =
        f (P.rootEmbedding (rho i)).1 := hPieceMap _
      _ = f (d.roots i) := by rfl
  have hLeftInjective :
      Function.Injective
        (fun i : Fin n => pLeft (P.rootEmbedding (rho i))) := by
    intro i j h
    apply hSourceRootInjective
    calc
      f (d.roots i) =
          jLeft (pLeft (P.rootEmbedding (rho i))) :=
        (hPieceRoots i).symm
      _ = jLeft (pLeft (P.rootEmbedding (rho j))) :=
        congrArg jLeft h
      _ = f (d.roots j) := hPieceRoots j
  have hRelLeft :=
    enumeratedRootClassCanonicalRelation_of_weak
      Root rho F P Left pLeft hpLeft hLeftInjective
  have hRelRight := hSharedLift hRelLeft
  exact geometricMinimalPieceFlip_of_canonicalRelation
    A d F hFA Target f hf Right jRight
    xsRight hRightRoot hRelRight

end AllThoseRamseyClasses.Lifts
