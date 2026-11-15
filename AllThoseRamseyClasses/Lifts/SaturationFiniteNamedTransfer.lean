import AllThoseRamseyClasses.Lifts.FullRangeSaturationConnected
import AllThoseRamseyClasses.Lifts.FullRangeSaturationFiniteCover
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceStrongAmalgamation
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceExactReduct
import AllThoseRamseyClasses.Lifts.FiniteFamilyConnectedJEP

/-!
# Realize a bounded saturated family as finite named forbidden sources

This makes the alternative finite FAMILY folded lift applicable to
the SAME OLD-LANGUAGE forbidden-free shadow as the original family.

In a finite native signature with a uniform original forbidden-source
size bound N, the full-range EHN saturation has a finite TYPE of
full-isomorphism representatives, with sizes at most N. Use every
member as a genuine FINITE NAMED source, and prove that avoidance
of that finite named family is EXACTLY avoidance of the saturated
family, hence of the ORIGINAL forbidden class.

This is a bridge to the existing finite-family all-closed-component
folded-lift strong-AP theory. It does NOT identify that ALTERNATIVE
folded lift with the 2019 minimal-separator canonical G-lift, or prove
the original unrestricted Claim 2.

The named-family packaging is in a small (Type 0) native signature,
as required by the existing FiniteNamedFunctionalSources API.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

/-- The exact finite list of COMPLETE native saturated source tables
on canonical Fin carriers. The index is itself the finite subtype
of genuine saturated structures, not an arbitrary external list. -/
noncomputable def boundedSaturationNamedFamily
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :
    FiniteNamedFunctionalSources L where
  Index := BoundedSaturatedFinRepresentatives F N
  finiteIndex := boundedSaturatedFinRepresentatives_finite F N
  Carrier := fun p => Fin p.1.val
  finiteCarrier := fun _ => inferInstance
  source := fun p => p.2.1

/-- Bounded full-isomorphism coverage implies exactly the same
forbidden-free class whether all saturated sources are tested
globally, or only their FINITELY MANY complete representatives
are tested via the existing finite named weak-EHN API.

The carrier of an arbitrary saturated source is not declared equal
to a Fin type: a genuinely FULL embedding from the representative
factors the EHN witness, preserving all old complete function fibres. -/
theorem avoidsBoundedSaturationNamed_iff
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hBound : ∀ {V : Type} (A : Structure L V),
      F A → Nat.card V ≤ N)
    {W : Type} (Target : Structure L W) :
    AvoidsFiniteNamedEHN (boundedSaturationNamedFamily L F N) Target ↔
      AvoidsGlobalFunctionalEHN (FullRangeEHNSaturation F) Target := by
  constructor
  · intro hNamed U Source _hFinite hSat f hf
    obtain ⟨p, e, _heSurj⟩ :=
      fullRangeEHNSaturation_bounded_fullIsoCover
        F N hBound Source hSat
    have hMap :
        (p.2.1).IsEHNHomomorphismEmbedding Target (f ∘ e) :=
      hf.comp e.isEHNHomomorphismEmbedding
    exact (hNamed p (f ∘ e)) hMap
  · intro hSat i f hf
    have hMember : FullRangeEHNSaturation F
        ((boundedSaturationNamedFamily L F N).source i) :=
      i.2.2
    exact (hSat ((boundedSaturationNamedFamily L F N).source i)
      ((boundedSaturationNamedFamily L F N).finiteCarrier i)
      hMember f) hf

/-- The finite named alternative folded lift has the exact ORIGINAL
forbidden-free shadow class, not merely that of the saturated family.
The added named tags and the original 2019 canonical relations are
different expansion signatures. -/
theorem avoidsBoundedSaturationNamed_iff_original
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hBound : ∀ {V : Type} (A : Structure L V),
      F A → Nat.card V ≤ N)
    {W : Type} (Target : Structure L W) :
    AvoidsFiniteNamedEHN (boundedSaturationNamedFamily L F N) Target ↔
      AvoidsGlobalFunctionalEHN F Target := by
  exact (avoidsBoundedSaturationNamed_iff L F N hBound Target).trans
    (avoids_fullRangeEHNSaturation_iff F Target)

/-- The original forbidden-free class is the EXACT old-language
reduct of the actual hereditary finite-named folded maximal-trace age.
This connects the saturation finite representative cover with the
already verified nonempty finite-fibre expansion theorem, rather than
merely asserting equality of two avoidance predicates. -/
theorem boundedSaturationNamed_maximalTrace_exact_reduct
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hBound : ∀ {V : Type} (A : Structure L V),
      F A → Nat.card V ≤ N)
    {W : Type} [Finite W] (A : Structure L W) :
    (∃ (Y : Structure
        (functionalLiftLanguageBig L
          (boundedSaturationNamedFamily L F N).ComponentTag
          (fun tag => tag.width (boundedSaturationNamedFamily L F N))) W),
      FiniteNamedTraceShadow
        (boundedSaturationNamedFamily L F N) Y = A ∧
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) Y) ↔
      AvoidsGlobalFunctionalEHN F A := by
  exact (finiteNamedMaximalTraceAge_exact_reduct
    (boundedSaturationNamedFamily L F N) A).trans
    (avoidsBoundedSaturationNamed_iff_original L F N hBound A)

/-- Every finite named saturated representative is nonempty and
connected whenever the original finite forbidden sources are.
The full-range image factorization and positive native Gaifman
incidences prove this, independently of bounded-source regularity. -/
theorem boundedSaturationNamed_connectedNonempty
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    FiniteNamedSourcesConnectedNonempty
      (boundedSaturationNamedFamily L F N) := by
  intro i
  have hSatConnected :
      GlobalForbiddenSourcesConnectedNonempty
        (FullRangeEHNSaturation F) :=
    fullRangeEHNSaturation_connectedNonempty F hConnected
  exact hSatConnected
    ((boundedSaturationNamedFamily L F N).source i)
    ((boundedSaturationNamedFamily L F N).finiteCarrier i)
    i.2.2

end AllThoseRamseyClasses.Lifts
