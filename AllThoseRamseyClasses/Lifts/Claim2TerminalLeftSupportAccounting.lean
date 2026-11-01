import AllThoseRamseyClasses.Lifts.Claim2IteratedContextualDescent
import AllThoseRamseyClasses.Lifts.ForbiddenWeakWitnessMinimization

/-!
# Track C — terminal A-support accounting for the original Claim 2

The original 2019 proof chooses an actual finite forbidden EHN
witness of MINIMAL *left*-exclusive SOURCE support and then proposes
B-to-A replacements of smaller pieces inside one outer mixed piece.

A successful B-to-A replacement can INCREASE the left support.
It would therefore be invalid to assume that intermediate states
remain left-minimal, or to invoke left minimality directly on the
local strict B-support decrease.

The mathematically sufficient invariant is different:

* B-exclusive SOURCE support INSIDE the transported outer context
  strictly decreases (already in Claim2ActualOneStepContextualFlip).
* A-exclusive SOURCE support OUTSIDE that context is exactly
  conserved, for every intermediate native full source replacement
  preserving the complement and its target map.
* The ORIGINAL outer piece contains at least one A-only source
  vertex.
* In the FINAL A-to-B replacement, the new context has NO A-only
  source vertex.

The finite-counting theorem below proves that, under these
conditions, final TOTAL A-source support is strictly smaller than
the ORIGINAL total A-source support. In particular it is irrelevant
how much intermediate left support grew inside the outer context.

The remaining geometric tasks are to prove that *every* desired
contextual step remains a genuine outer geometric piece, to
recover a terminal A-to-B full native flip, and to show this final
flip has no A-only vertex in its transported context. These are
NOT assumed as automatically established by finite descent.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A strict final LEFT-source-support drop relative to the
ORIGINAL state: the original context contains an A-only vertex,
the final context contains none, and the number of A-only source
vertices OUTSIDE the two contexts is exactly equal.

No condition on the intermediate A-only support counts enters. -/
theorem finiteSourceSupport_terminalLeftDrop_of_outsideEq
    {V W T : Type v}
    [Finite V] [Finite W]
    (f : V → T) (g : W → T)
    (OldContext : Set V) (FinalContext : Set W)
    (AOnly : Set T)
    (hOldInside : ∃ v : V, v ∈ OldContext ∧ f v ∈ AOnly)
    (hFinalNoA : ∀ w : W, w ∈ FinalContext → g w ∉ AOnly)
    (hOutsideEq :
      Nat.card {w : W //
        w ∉ FinalContext ∧ g w ∈ AOnly} =
      Nat.card {v : V //
        v ∉ OldContext ∧ f v ∈ AOnly}) :
    Nat.card {w : W // g w ∈ AOnly} <
      Nat.card {v : V // f v ∈ AOnly} := by
  classical
  obtain ⟨v, hvContext, hvA⟩ := hOldInside
  have hPositive :
      0 < Nat.card {v : V //
        v ∈ OldContext ∧ f v ∈ AOnly} := by
    letI : Fintype {v : V //
      v ∈ OldContext ∧ f v ∈ AOnly} := Fintype.ofFinite _
    have hNonempty : Nonempty {v : V //
        v ∈ OldContext ∧ f v ∈ AOnly} :=
      ⟨⟨v, hvContext, hvA⟩⟩
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_pos_iff.mpr hNonempty)
  have hFinalZero :
      Nat.card {w : W //
        w ∈ FinalContext ∧ g w ∈ AOnly} = 0 := by
    letI : Fintype {w : W //
      w ∈ FinalContext ∧ g w ∈ AOnly} := Fintype.ofFinite _
    haveI : IsEmpty {w : W //
        w ∈ FinalContext ∧ g w ∈ AOnly} := ⟨by
      intro w
      exact (hFinalNoA w.1 w.2.1) w.2.2⟩
    simpa only [Nat.card_eq_fintype_card] using
      (Fintype.card_eq_zero :
        Fintype.card {w : W //
          w ∈ FinalContext ∧ g w ∈ AOnly} = 0)
  have hOldSplit :=
    finiteSourceSupport_card_split f OldContext AOnly
  have hFinalSplit :=
    finiteSourceSupport_card_split g FinalContext AOnly
  omega

/-- The concrete source-geometric ONE-STEP exterior-support
invariant for ANY chosen target region, including the original
LEFT-exclusive region. The old outer context is the ACTUAL
geometric piece P; the new context is all of the replacement
inner piece together with precisely the retained complement
vertices which belonged to P.

The equality counts SOURCE vertices and refers to the SAME full
native replacement source, the SAME two maps, and exactly the
complete complement whose target map is unchanged. It does not
require a new geometric-piece recognition, outer profile
preservation or global weak-target-map injectivity. -/
theorem geometricInnerSubpiece_outsideSupport_card_eq
    {V W UT : Type}
    [Finite V] [Finite W]
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerInside :
      geometricPieceVertices Old d ⊆ geometricPieceVertices Old P)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (f : V → UT) (g : W → UT)
    (TargetSet : Set UT)
    (hSameComplement :
      ∀ b : (geometricGlobalComplementChart Old d).Carrier,
        g (iE b) = f b.1) :
    Nat.card {w : W //
      w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) ∧
      g w ∈ TargetSet} =
    Nat.card {v : V //
      v ∉ geometricPieceVertices Old P ∧ f v ∈ TargetSet} := by
  let E := geometricGlobalComplementChart Old d
  letI : Finite E.Carrier :=
    Finite.of_injective (fun b : E.Carrier => b.1)
      (by intro a b hab; exact Subtype.ext hab)
  have hRootInP : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P := by
    intro i
    exact hInnerInside (Or.inl ⟨i, rfl⟩)
  have hOutside :=
    fullFreeAmalgam_contextOutside_support_card_eq
      (geometricGlobalSource_freeDiagram Old d)
      hNewFree
      (oldOuterContextInInnerComplement Old P d)
      (oldOuterContext_contains_innerRoot Old P d hRootInP)
      f g TargetSet hSameComplement
  have hOldCarrier :=
    geometricInnerSubpiece_oldOuterContext_eq
      Old P d hInnerInside
  rw [← hOldCarrier]
  exact hOutside

/-- The outside-A count is invariant along ANY FINITE sequence
of genuine contextual steps, if it is invariant for each step.
The state may package different finite native source carrier types;
there is no global injection or chosen common source universe. -/
theorem claim2_outsideLeftCount_eq_of_reachable
    {State : Type*}
    (Step : State → State → Prop)
    (outsideLeftCount : State → ℕ)
    (hSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    {start finish : State}
    (hReach : Relation.ReflTransGen Step start finish) :
    outsideLeftCount finish = outsideLeftCount start := by
  induction hReach with
  | refl => rfl
  | @tail a b hab hbc ih =>
      exact (hSame hbc).trans ih

/-- Add the EXACT exterior-left-support invariant to the
previously checked abstract natural-number B-descent theorem.

The terminal state is actually REACHABLE by finitely many steps;
its exterior A-count equals the original. It is NOT presumed that
the intermediate left support is minimal or monotone. -/
theorem claim2_exists_terminal_with_constant_outsideLeft
    {State : Type*}
    (Valid : State → Prop)
    (Step : State → State → Prop)
    (localBCount outsideLeftCount : State → ℕ)
    (hStep : ∀ {s t : State},
      Valid s → Step s t →
        Valid t ∧ localBCount t < localBCount s)
    (hOutsideSame : ∀ {s t : State},
      Step s t → outsideLeftCount t = outsideLeftCount s)
    {initial : State} (hInitial : Valid initial) :
    ∃ terminal : State,
      Valid terminal ∧
      Relation.ReflTransGen Step initial terminal ∧
      outsideLeftCount terminal = outsideLeftCount initial ∧
      ¬ ∃ next : State, Step terminal next := by
  obtain ⟨terminal, htValid, hReach, hNoNext⟩ :=
    claim2_exists_terminal_of_strict_localB_descent
      Valid Step localBCount hStep hInitial
  exact ⟨terminal, htValid, hReach,
    claim2_outsideLeftCount_eq_of_reachable
      Step outsideLeftCount hOutsideSame hReach,
    hNoNext⟩

/-- The final contextual A-to-B flip contradicts the ORIGINAL
support-minimal forbidden EHN witness as soon as it has erased
all left-exclusive source vertices from its transported context,
while leaving unchanged the exterior left-exclusive SOURCE count.

No intermediate forbidden witness is assumed left-minimal.
The new source may have a completely different finite carrier. -/
theorem minimalForbiddenEHNWitness_no_terminalLeftClearingFlip
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UT : Type} (Target : Structure L UT)
    (AOnly : Set UT)
    (w : ForbiddenEHNWitness F Target)
    (hwMin : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount AOnly ≤ v.sourceSupportCount AOnly)
    (OldContext : Set w.Carrier)
    (hOldInside : ∃ v : w.Carrier,
      v ∈ OldContext ∧ w.toTarget v ∈ AOnly)
    {W : Type} (New : Structure L W)
    (hFinite : Finite W) (hForbidden : F New)
    (g : W → UT)
    (hg : New.IsEHNHomomorphismEmbedding Target g)
    (FinalContext : Set W)
    (hFinalNoA : ∀ v : W,
      v ∈ FinalContext → g v ∉ AOnly)
    (hOutsideEq :
      Nat.card {v : W //
        v ∉ FinalContext ∧ g v ∈ AOnly} =
      Nat.card {v : w.Carrier //
        v ∉ OldContext ∧ w.toTarget v ∈ AOnly}) : False := by
  letI : Finite w.Carrier := w.finiteCarrier
  letI : Finite W := hFinite
  let final : ForbiddenEHNWitness F Target := {
    Carrier := W
    finiteCarrier := hFinite
    source := New
    forbidden := hForbidden
    toTarget := g
    homEmbedding := hg
  }
  have hStrict :
      final.sourceSupportCount AOnly <
        w.sourceSupportCount AOnly := by
    change Nat.card {v : W // g v ∈ AOnly} <
      Nat.card {v : w.Carrier // w.toTarget v ∈ AOnly}
    exact finiteSourceSupport_terminalLeftDrop_of_outsideEq
      w.toTarget g OldContext FinalContext AOnly
      hOldInside hFinalNoA hOutsideEq
  exact (minimalForbiddenEHNWitness_no_strict_drop
    AOnly w hwMin final) hStrict

end AllThoseRamseyClasses.Lifts
