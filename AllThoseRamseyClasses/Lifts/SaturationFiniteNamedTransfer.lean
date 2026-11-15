import AllThoseRamseyClasses.Lifts.FullRangeSaturationConnected
import AllThoseRamseyClasses.Lifts.FullRangeSaturationFiniteCover
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceStrongAmalgamation
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceExactReduct
import AllThoseRamseyClasses.Lifts.FiniteFamilyConnectedJEP
import AllThoseRamseyClasses.Lifts.FiniteFamilyOrderedStrongAmalgamation

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

/-- The alternative all-closed-component folded signature for a
finite named list of all bounded saturated native structures.
This is a DIFFERENT language from the original 2019 global
minimal-separator canonical lift. -/
abbrev boundedSaturationFoldedLanguage
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol] :=
  functionalLiftLanguageBig L
    (boundedSaturationNamedFamily L F N).ComponentTag
    (fun tag => tag.width (boundedSaturationNamedFamily L F N))

/-- Real STRONG amalgamation for the hereditary maximal-trace age
of the alternative finite-NAMED saturated folded expansion.

This is a genuine specialization of the separately verified
finite-named strong-AP theorem. The previous exact-reduct theorem
identifies this age's old-language shadow with Forb_EHN(F) provided
the original finite forbidden sources have the uniform bound N.
It is NOT the printed 2019 minimal-root lift theorem. -/
theorem boundedSaturationFoldedAge_strongAmalgamation
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    {VX VY VZ : Type}
    (X : Structure (boundedSaturationFoldedLanguage L F N) VX)
    (Y : Structure (boundedSaturationFoldedLanguage L F N) VY)
    (Z : Structure (boundedSaturationFoldedLanguage L F N) VZ)
    (hY : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Y)
    (hZ : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Z)
    (fY : Structure.Embedding X Y)
    (fZ : Structure.Embedding X Z) :
    ∃ (VT : Type)
      (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) T ∧
        ∃ (jY : Structure.Embedding Y T)
          (jZ : Structure.Embedding Z T),
          ∀ y : VY, ∀ z : VZ,
            jY y = jZ z ↔
              ∃ x : VX, y = fY x ∧ z = fZ x := by
  exact finiteNamedMaximalTraceAge_strongAmalgamation
    (boundedSaturationNamedFamily L F N) X Y Z hY hZ fY fZ

/-- Precompactness of the alternative saturated folded age on
each fixed old native structure: its complete added-relation fibre
is FINITE, including arbitrary native partial functions. -/
theorem boundedSaturationFoldedAge_fibre_finite
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    {W : Type} [Finite W] (A : Structure L W) :
    Finite (FiniteNamedMaximalTraceFibre
      (boundedSaturationNamedFamily L F N) A) :=
  finiteNamedMaximalTraceFibre_finite
    (boundedSaturationNamedFamily L F N) A

/-- The precompact expansion fibre is NONEMPTY exactly over the
ORIGINAL forbidden-free native structures, provided all original
finite forbidden witnesses obey the uniform vertex bound N. -/
theorem boundedSaturationFoldedAge_fibre_nonempty_iff_original
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hBound : ∀ {V : Type} (A : Structure L V),
      F A → Nat.card V ≤ N)
    {W : Type} [Finite W] (A : Structure L W) :
    Nonempty (FiniteNamedMaximalTraceFibre
      (boundedSaturationNamedFamily L F N) A) ↔
        AvoidsGlobalFunctionalEHN F A := by
  exact (finiteNamedMaximalTraceFibre_nonempty_iff_avoids
    (boundedSaturationNamedFamily L F N) A).trans
    (avoidsBoundedSaturationNamed_iff_original L F N hBound A)

/-- Actual JEP of the alternative saturated finite-family folded
age when the original finite forbidden sources are connected and
nonempty and the native language has POSITIVE arities. Nullary
native compatibility is NOT silently assumed. -/
theorem boundedSaturationFoldedAge_jointEmbedding_positiveArity
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {VY VZ : Type}
    (Y : Structure (boundedSaturationFoldedLanguage L F N) VY)
    (Z : Structure (boundedSaturationFoldedLanguage L F N) VZ)
    (hY : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Y)
    (hZ : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Z) :
    ∃ (VT : Type)
      (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) T ∧
        ∃ (jY : Structure.Embedding Y T)
          (jZ : Structure.Embedding Z T), True := by
  exact finiteNamedMaximalTraceAge_JEP_connected_positiveArity
    (boundedSaturationNamedFamily L F N)
    hArity (boundedSaturationNamed_connectedNonempty L F N hConnected)
    Y Z hY hZ

/-- Ordered genuine strong amalgamation for the ALTERNATIVE
finite-named saturated folded age. Existing full expanded finite
strong amalgamation is followed by the already proved order
extension on the SAME target vertices, preserving exact overlaps.
This is NOT the original 2019 minimal-separator lift. -/
theorem boundedSaturationFoldedAge_orderedStrongAmalgamation
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    {VX VY VZ : Type}
    [LinearOrder VX] [LinearOrder VY] [LinearOrder VZ]
    (X : Structure (boundedSaturationFoldedLanguage L F N) VX)
    (Y : Structure (boundedSaturationFoldedLanguage L F N) VY)
    (Z : Structure (boundedSaturationFoldedLanguage L F N) VZ)
    (hY : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Y)
    (hZ : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Z)
    (fY : Structure.Embedding X.withLinearOrder Y.withLinearOrder)
    (fZ : Structure.Embedding X.withLinearOrder Z.withLinearOrder) :
    ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
      (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) T ∧
        ∃ (jY : Structure.Embedding Y.withLinearOrder
            (@Structure.withLinearOrder _ VT T o.toLT))
          (jZ : Structure.Embedding Z.withLinearOrder
            (@Structure.withLinearOrder _ VT T o.toLT)),
          ∀ y : VY, ∀ z : VZ,
            jY y = jZ z ↔
              ∃ x : VX, y = fY x ∧ z = fZ x := by
  exact finiteNamedMaximalTraceAge_orderedStrongAmalgamation
    (boundedSaturationNamedFamily L F N)
    X Y Z hY hZ fY fZ

/-- Joint embedding under the actual compatible FULL empty-root
condition, without assuming all native arities positive. This
handles nullary languages when the required compatibility is given,
rather than incorrectly declaring all nullary shadows compatible. -/
theorem boundedSaturationFoldedAge_jointEmbedding_of_emptyRoots
    (L : Language)
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    [Finite L.RelSymbol] [Finite L.FuncSymbol]
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hEmpty : GlobalNativeCommonEmptyRoots
      (fun {V : Type} (A : Structure L V) =>
        AvoidsFiniteNamedEHN (boundedSaturationNamedFamily L F N) A))
    {VY VZ : Type}
    (Y : Structure (boundedSaturationFoldedLanguage L F N) VY)
    (Z : Structure (boundedSaturationFoldedLanguage L F N) VZ)
    (hY : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Y)
    (hZ : IsFiniteNamedMaximalTrace
      (boundedSaturationNamedFamily L F N) Z) :
    ∃ (VT : Type)
      (T : Structure (boundedSaturationFoldedLanguage L F N) VT),
      IsFiniteNamedMaximalTrace
        (boundedSaturationNamedFamily L F N) T ∧
        ∃ (jY : Structure.Embedding Y T)
          (jZ : Structure.Embedding Z T), True := by
  exact finiteNamedMaximalTraceAge_JEP_connected_of_emptyRoots
    (boundedSaturationNamedFamily L F N)
    (boundedSaturationNamed_connectedNonempty L F N hConnected)
    hEmpty Y Z hY hZ

end AllThoseRamseyClasses.Lifts
