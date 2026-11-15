import AllThoseRamseyClasses.Lifts.EHNPrintedTupleSourceSurgeryDescent
import Mathlib.Data.Fintype.Card

/-!
# Track D: strict ordered source seam-collision descent under genuine surjective source contractions

This is the exact counterpart of occupied-seam map recolouring:
instead of moving one OLD source vertex to a new target value,
we quotient a pair of OLD source vertices whose target seam
images already coincide, using an actual surjection h:Old→New
and a factoring target map g:New→Target.

A section s of h injects all NEW ordered distinct source seam
collision pairs into OLD ordered source collision pairs.
If h(a)=h(b) for two DISTINCT ORIGINAL source vertices a,b with
f(a) in Seam, the old pair (a,b) is NOT in this section image.
Thus the new original-source ordered pair count STRICTLY drops.
This works with arbitrary other source collisions and does NOT
assume the target seam has spare vertices.

A full embedding of a forbidden piece P↪New can only reduce
the original ordered collision pair count further.

This is a numerical source-carrier statement; EHN/full
native structure and forbidden-family membership of the
replacement must be supplied separately. Neither a weak
quotient nor a positive homomorphism is silently declared full.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

/-- Genuine strict descent of ORIGINAL ordered distinct-source
seam-collision pairs under a surjective source map h which
identifies a pair of distinct old source vertices already
mapped into the common target seam.

The factoring condition g∘h=f proves that the contracted pair
had equal old target images, while the section of h proves
no new collisions are introduced between distinct NEW source
vertices. No native EHN assumption is needed for this count. -/
theorem finiteSurjectiveSourceContraction_strictSeamCollisionDrop
    {V W UT : Type} [Finite V] [Finite W]
    (h : V → W) (hSurj : Function.Surjective h)
    (f : V → UT) (g : W → UT)
    (hFactor : ∀ x : V, g (h x) = f x)
    (Seam : Set UT)
    (a b : V) (hab : a ≠ b)
    (hCollapse : h a = h b)
    (hSeam : f a ∈ Seam) :
    Nat.card {p : W × W //
      p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
    Nat.card {p : V × V //
      p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧ f p.1 ∈ Seam} := by
  classical
  letI : Fintype V := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  let New : Type := {p : W × W //
    p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam}
  let Old : Type := {p : V × V //
    p.1 ≠ p.2 ∧ f p.1 = f p.2 ∧ f p.1 ∈ Seam}
  let s : W → V := fun z => Classical.choose (hSurj z)
  have hs (z : W) : h (s z) = z :=
    Classical.choose_spec (hSurj z)
  have hsInj : Function.Injective s := by
    intro x y hEq
    calc
      x = h (s x) := (hs x).symm
      _ = h (s y) := congrArg h hEq
      _ = y := hs y
  have hOldAt (z : W) : f (s z) = g z := by
    calc
      f (s z) = g (h (s z)) := (hFactor (s z)).symm
      _ = g z := congrArg g (hs z)
  let push : New → Old := fun p =>
    ⟨(s p.1.1, s p.1.2), by
      have hne : s p.1.1 ≠ s p.1.2 := by
        intro hEq
        exact p.2.1 (hsInj hEq)
      have hTargetEq : f (s p.1.1) = f (s p.1.2) := by
        calc
          f (s p.1.1) = g p.1.1 := hOldAt _
          _ = g p.1.2 := p.2.2.1
          _ = f (s p.1.2) := (hOldAt _).symm
      have hTargetSeam : f (s p.1.1) ∈ Seam := by
        rw [hOldAt]
        exact p.2.2.2
      exact ⟨hne, hTargetEq, hTargetSeam⟩⟩
  have hPushInj : Function.Injective push := by
    intro p q hpq
    have hpqVal : (s p.1.1, s p.1.2) =
        (s q.1.1, s q.1.2) := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext
    · apply hsInj
      exact congrArg Prod.fst hpqVal
    · apply hsInj
      exact congrArg Prod.snd hpqVal
  have hfSame : f a = f b := by
    calc
      f a = g (h a) := (hFactor a).symm
      _ = g (h b) := congrArg g hCollapse
      _ = f b := hFactor b
  let bad : Old := ⟨(a, b), hab, hfSame, hSeam⟩
  have hPushNotSurj : ¬ Function.Surjective push := by
    intro hPushSurj
    obtain ⟨p, hp⟩ := hPushSurj bad
    have hpVal : (s p.1.1, s p.1.2) = (a, b) :=
      congrArg Subtype.val hp
    have ha : s p.1.1 = a := congrArg Prod.fst hpVal
    have hb : s p.1.2 = b := congrArg Prod.snd hpVal
    have hp1 : p.1.1 = h a := by
      calc
        p.1.1 = h (s p.1.1) := (hs _).symm
        _ = h a := congrArg h ha
    have hp2 : p.1.2 = h b := by
      calc
        p.1.2 = h (s p.1.2) := (hs _).symm
        _ = h b := congrArg h hb
    exact p.2.1 (hp1.trans (hCollapse.trans hp2.symm))
  letI : Fintype New := Fintype.ofFinite _
  letI : Fintype Old := Fintype.ofFinite _
  change Nat.card New < Nat.card Old
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_not_surjective
      push hPushInj hPushNotSurj)

/-- A genuine injection of ORIGINAL source carriers cannot
increase the number of ordered distinct-source seam collision
pairs. The target map on the small source is the literal
composition g∘e; no full native-structure claim is used. -/
theorem finiteSourceInjection_seamCollisionPairs_le
    {Z W UT : Type} [Finite Z] [Finite W]
    (e : Z → W) (he : Function.Injective e)
    (g : W → UT) (Seam : Set UT) :
    Nat.card {p : Z × Z //
      p.1 ≠ p.2 ∧
      (g ∘ e) p.1 = (g ∘ e) p.2 ∧
      (g ∘ e) p.1 ∈ Seam} ≤
    Nat.card {p : W × W //
      p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} := by
  classical
  letI : Fintype Z := Fintype.ofFinite _
  letI : Fintype W := Fintype.ofFinite _
  let Small : Type := {p : Z × Z //
    p.1 ≠ p.2 ∧
    (g ∘ e) p.1 = (g ∘ e) p.2 ∧
    (g ∘ e) p.1 ∈ Seam}
  let Large : Type := {p : W × W //
    p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam}
  let push : Small → Large := fun p =>
    ⟨(e p.1.1, e p.1.2), by
      have hd : e p.1.1 ≠ e p.1.2 := by
        intro heq
        exact p.2.1 (he heq)
      exact ⟨hd, p.2.2.1, p.2.2.2⟩⟩
  have hInj : Function.Injective push := by
    intro p q hpq
    have heq : (e p.1.1, e p.1.2) =
        (e q.1.1, e q.1.2) := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext
    · exact he (congrArg Prod.fst heq)
    · exact he (congrArg Prod.snd heq)
  letI : Fintype Small := Fintype.ofFinite _
  letI : Fintype Large := Fintype.ofFinite _
  change Nat.card Small ≤ Nat.card Large
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_le_of_injective push hInj)

end AllThoseRamseyClasses.Lifts
