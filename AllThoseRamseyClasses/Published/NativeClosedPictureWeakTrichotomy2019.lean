import AllThoseRamseyClasses.Published.NativeActualWeakTrichotomy2019
import AllThoseRamseyClasses.Published.NativeClosedPictureWeakRest2019

/-!
# Paper-faithful protected CLOSED Picture -> EXACT weak native trichotomy

Merged PR #153 proves a true finite native active-history trichotomy
for a maximal intrinsic U-rank source with an ORDINARY map into the
actual native attachment. The 2019 corrected Picture construction,
however, supplies a PROTECTED projection from a U-CLOSED full Picture;
each local test is the possibly nonclosed induced weak restriction
to an original finite vertex subset S.

This file bridges those quantifiers without inventing a weak-source
closedness assumption or an ordinary map of an arbitrary protected
weak source:

1. the protected map from the CLOSED FULL Picture is an ordinary
   homomorphism-embedding on the full Picture;
2. restricting it to C|S gives the ordinary source map required by
   the real native finite-history theorem;
3. for each exact weak S with maximal intrinsic U-rank and |S|<=j+1,
   either it is actually K-completable, or it has an ordinary
   INJECTIVE map to the previous Old Picture, or it has a proper
   exact source free cut into sides with <=j vertices.

Only the prior exact W_j(Old) weak completion invariant is used in
the common-coordinate collision branch. No rank-j closed-hull
completion or global HJ parameter is assumed.

This is a fully correct 2019 local-test interface, NOT the missing
native Picture successor constructor. The injective old-map and
transverse free-cut alternatives are not themselves completions,
and the nonmaximal-rank active-source branch remains OPEN.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- For each original exact induced finite weak test of a corrected
U-CLOSED full Picture, maximal intrinsic U-size and |S|<=j+1 imply
the honest native trichotomy. The weak test itself is NOT required
closed, nor is the temporary target attachment semi-closed. -/
theorem native2019_closed_picture_exact_weak_trichotomy
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Finite U] [Finite Q] [Finite V]
    (C : RelStructure L U)
    (hC : IsUClosed rules C)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules C
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (j : ℕ)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.toRelStructure.induce (↑T : Set V)))
    (S : Finset U)
    (hCard : S.card ≤ j+1)
    (hMax : USize rules (C.induce (↑S : Set U)) = S.card) :
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set U)) ∨
      (∃ q : (↑S : Set U) → V,
        (C.induce (↑S : Set U)).IsHomomorphismEmbedding
          Old.toRelStructure q ∧ Function.Injective q) ∨
      (∃ d : ProperFreeDecomposition (C.induce (↑S : Set U)),
        Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  have hpAbstract : IsClosedUHomomorphismEmbedding rules C
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hpOrd : C.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsClosedUHomomorphismEmbedding.toHomomorphismEmbedding_of_closed
      hpAbstract hC
  have hpTest : (C.induce (↑S : Set U)).IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines))
      (fun x : (↑S : Set U) => p x.1) :=
    hpOrd.comp (inclusion C (↑S : Set U)).isHomomorphismEmbedding
  have hMaxCard : USize rules (C.induce (↑S : Set U)) =
      Fintype.card (↑S : Set U) := by
    simpa using hMax
  have hFCard : Fintype.card (↑S : Set U) ≤ j+1 := by
    simpa using hCard
  exact native2019_actual_active_weaksize_trichotomy
    (C.induce (↑S : Set U)) hMaxCard
    Old alpha A hAK hAIrred hRestricted hPower lines
    (fun x : (↑S : Set U) => p x.1) hpTest
    j hFCard hOldWeak

end AllThoseRamseyClasses.Published
