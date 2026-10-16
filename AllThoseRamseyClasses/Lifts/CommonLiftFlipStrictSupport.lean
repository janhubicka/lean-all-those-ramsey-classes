import AllThoseRamseyClasses.Lifts.CommonFullGlobalPieceFlip
import AllThoseRamseyClasses.Lifts.FlipSupportStrictDecrease
import AllThoseRamseyClasses.Lifts.WeakSourceFreeAmalgamPartition
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram

/-!
# Conditional Claim 1: an actual common-lift piece flip strictly reduces support

Combine the genuine global quotient-indexed canonical piece relation,
the common FULL lifted root X, the actual forbidden-source free-amalgam
diagram, and the exact finite support-counting theorem.

The output is a new member of the forbidden family with a weak
homomorphism-embedding to the SAME ambient free amalgam and a STRICTLY
smaller number of source vertices mapped into Left minus X.

The hypotheses are exposed: the selected old piece maps weakly into
Left, its root image is injective, and the common FULL lifted X is
already supplied. The original 2019 proof does not justify root-image
injectivity from arbitrary weak maps; this theorem never asserts it.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- The true exclusive-left region of a target free amalgam, expressed
without reference to a particular forbidden-source map. -/
def fullFreeLeftExclusiveTarget
    {UX UA UT : Type}
    {X : Structure L UX} {Left : Structure L UA}
    {Target : Structure L UT}
    (iLeft : Structure.Embedding X Left)
    (jLeft : Structure.Embedding Left Target) : Set UT :=
  {z | z ∈ Set.range jLeft ∧
    z ∉ Set.range (jLeft.comp iLeft)}

/-- No point of the embedded RIGHT target side belongs to the
exclusive-left target set: an overlap would lie in the full root. -/
theorem freeRight_avoids_fullLeftExclusiveTarget
    {UX UA UB UT : Type}
    {X : Structure L UX} {Left : Structure L UA}
    {Right : Structure L UB} {Target : Structure L UT}
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (hfree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (b : UB) :
    jRight b ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
  rintro ⟨⟨a, ha⟩, hnotRoot⟩
  have hab : jLeft a = jRight b := ha.symm
  obtain ⟨r, hrLeft, _hrRight⟩ := (hfree.overlap a b).mp hab
  apply hnotRoot
  refine ⟨r, ?_⟩
  change jLeft (iLeft r) = jRight b
  calc
    jLeft (iLeft r) = jLeft a := congrArg jLeft hrLeft.symm
    _ = jRight b := hab

/-- The exact exclusive-left SOURCE partition is the pullback of
the exclusive-left target set. -/
theorem weakFreeLeftPart_iff_targetExclusive
    {UX UA UT U : Type}
    {X : Structure L UX} {Left : Structure L UA}
    {Target : Structure L UT}
    (iLeft : Structure.Embedding X Left)
    (jLeft : Structure.Embedding Left Target)
    (f : U → UT) (x : U) :
    x ∈ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f ↔
      f x ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
  constructor
  · rintro ⟨⟨a, ha⟩, hnotRoot⟩
    exact ⟨⟨a, ha.symm⟩, hnotRoot⟩
  · rintro ⟨⟨a, ha⟩, hnotRoot⟩
    exact ⟨⟨a, ha.symm⟩, hnotRoot⟩

/-- The fully verified conditional finite-support consequence of
the ACTUAL geometric global canonical flip: if a chosen component
contains a source vertex mapped Left-only, the replacement forbidden
source has strictly fewer Left-only SOURCE vertices.

Only the weak source map is assumed; it may have collisions outside
the explicitly injective selected ordered ROOT. -/
theorem geometricGlobalCommonFullLiftFlip_strict_leftSupport
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hFiniteF : ∀ {W : Type} (A : Structure L W), F A → Finite W)
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
    (hTargetFree : Structure.IsFreeAmalgam iLeft iRight jLeft jRight)
    (hCommon : CommonGlobalCanonicalLift F X Left Right iLeft iRight)
    (pLeft : (geometricGlobalFunctionalChart Forbidden d).ext.Carrier → UA)
    (hpLeft : Structure.IsEHNHomomorphismEmbedding
      (geometricGlobalFunctionalChart Forbidden d).ext.str
      Left pLeft)
    (hPieceMap : ∀ z :
      (geometricGlobalFunctionalChart Forbidden d).ext.Carrier,
      jLeft (pLeft z) = f z.1)
    (xsX : Fin n → UX)
    (hRootLeft : ∀ i : Fin n,
      pLeft ((geometricGlobalFunctionalChart Forbidden d).ext.rootEmbedding i)
        = iLeft (xsX i))
    (hRootImageInjective : Function.Injective
      (fun i : Fin n => f (d.roots i)))
    (oldVertex : V)
    (hvComponent : oldVertex ∈
      functionalComponentFrom Forbidden (Set.range d.roots) d.left)
    (hvLeft : oldVertex ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) :
    ∃ (W : Type) (New : Structure L W),
      F New ∧
      ∃ flip : W → UT,
        New.IsEHNHomomorphismEmbedding Target flip ∧
        Nat.card {w : W //
          flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
        Nat.card {v : V //
          f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
  classical
  have hTargetAgree (r : UX) :
      jLeft (iLeft r) = jRight (iRight r) :=
    (hTargetFree.overlap (iLeft r) (iRight r)).mpr
      ⟨r, rfl, rfl⟩
  obtain ⟨Q, _hEq, g, _hg, _hRoot,
      W, New, hNewForbidden, iQ, iT,
      hNewFree, flip, hFlip, hFlipQ, hFlipT⟩ :=
    geometricGlobalCommonFullLiftFlip
      F Forbidden hFinite hForbidden d hn
      Target f hf Left Right jLeft jRight
      X iLeft iRight hCommon hTargetAgree
      pLeft hpLeft hPieceMap xsX hRootLeft hRootImageInjective
  let T := geometricGlobalComplementChart Forbidden d
  let iOldT :=
    functionalComponentComplementEmbedding Forbidden
      (Set.range d.roots) d.minimal.1 d.left
  letI : Fintype V := Fintype.ofFinite V
  letI : Finite W := hFiniteF New hNewForbidden
  letI : Fintype W := Fintype.ofFinite W
  letI : Finite T.Carrier :=
    Finite.of_injective (fun b : T.Carrier => b.1) (by
      intro a b hab
      exact Subtype.ext hab)
  letI : Fintype T.Carrier := Fintype.ofFinite T.Carrier
  have hOldRight : ∀ b : T.Carrier,
      f (iOldT b) = f b.1 := by
    intro b
    rfl
  have hOutside : ∀ b : T.Carrier,
      oldVertex ≠ iOldT b := by
    intro b hb
    have hv : oldVertex = b.1 := hb
    have hbComponent : b.1 ∈
        functionalComponentFrom Forbidden (Set.range d.roots)
          d.left := hv ▸ hvComponent
    exact b.2 hbComponent
  have hNewLeftAvoid : ∀ a : Q.Carrier,
      flip (iQ a) ∉ fullFreeLeftExclusiveTarget iLeft jLeft := by
    intro a
    rw [hFlipQ a]
    exact freeRight_avoids_fullLeftExclusiveTarget
      iLeft iRight jLeft jRight hTargetFree (g a)
  have hOldLeftTarget :
      f oldVertex ∈ fullFreeLeftExclusiveTarget iLeft jLeft :=
    (weakFreeLeftPart_iff_targetExclusive iLeft jLeft f oldVertex).mp
      hvLeft
  have hStrict :
      Nat.card {w : W //
        flip w ∈ fullFreeLeftExclusiveTarget iLeft jLeft} <
      Nat.card {v : V //
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft} := by
    exact flipExclusiveSupport_strict_decrease
      (iOldR := iOldT)
      (iNewL := iQ)
      (iNewR := iT)
      (sNewL := Q.rootEmbedding)
      (sRight := T.rootEmbedding)
      hNewFree f flip (fun b : T.Carrier => f b.1)
      hOldRight hFlipT
      (fullFreeLeftExclusiveTarget iLeft jLeft)
      hNewLeftAvoid oldVertex hOldLeftTarget hOutside
  exact ⟨W, New, hNewForbidden, flip, hFlip, hStrict⟩

end AllThoseRamseyClasses.Lifts
