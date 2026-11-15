import AllThoseRamseyClasses.Lifts.FullRangeEHNSaturation
import AllThoseRamseyClasses.Lifts.GlobalConnectedPositiveArityJEP

/-!
# Connectedness survives native full-range EHN saturation

This is an independent missing proof obligation in the repaired
original Section 3 argument: if each ORIGINAL forbidden source is
nonempty and Gaifman-connected, then so is every finite saturated
forbidden source.

The proof applies to functional languages too. It uses the previously
proved native Gaifman-edge projection of weak homomorphisms, allowing an
edge either to survive or to collapse to a vertex, and actual
VERTEX-surjectivity of the saturation witness.

No claim that an arbitrary native EHN map has a function-closed range
is made; no original Claim 2, strong AP, Ramsey, or arbitrary-regular
family statement follows.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every surjective native EHN image of a nonempty connected
source is again nonempty and connected in its COMPLETE Gaifman
graph, including positive native set-function incidences.

Only positive-incidence preservation is used: adjacent source
vertices may become equal, but an edge cannot disappear while
its endpoints remain distinct. -/
theorem gaifmanConnected_of_surjectiveEHN
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hSurj : Function.Surjective f)
    (hNonempty : Nonempty V)
    (hConnected : ∀ x y : V,
      Relation.ReflTransGen (GaifmanAdjacent A.graph) x y) :
    Nonempty W ∧
      ∀ a b : W,
        Relation.ReflTransGen (GaifmanAdjacent B.graph) a b := by
  have hPath :
      ∀ {x y : V},
        Relation.ReflTransGen (GaifmanAdjacent A.graph) x y →
        Relation.ReflTransGen
          (GaifmanAdjacent B.graph) (f x) (f y) := by
    intro x y h
    induction h with
    | refl =>
        exact Relation.ReflTransGen.refl
    | @tail a b hab hedge ih =>
        rcases weakFunctionalGaifmanAdjacent_map hf.1 hedge with
          hEqual | hAdjacent
        · simpa only [hEqual] using ih
        · exact Relation.ReflTransGen.tail ih hAdjacent
  constructor
  · obtain ⟨v⟩ := hNonempty
    exact ⟨f v⟩
  · intro a b
    obtain ⟨x, rfl⟩ := hSurj a
    obtain ⟨y, rfl⟩ := hSurj b
    exact hPath (hConnected x y)

/-- Connectedness and nonemptiness of ALL original finite
forbidden sources pass to the explicit vertex-surjective
EHN saturation, with NO assumption on native function symbols. -/
theorem fullRangeEHNSaturation_connectedNonempty
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    GlobalForbiddenSourcesConnectedNonempty
      (FullRangeEHNSaturation F) := by
  intro U Source _hFinite hSat
  obtain ⟨V, Original, hFiniteV, hOriginal, q, hq, hSurj⟩ := hSat
  obtain ⟨hNonempty, hPath⟩ :=
    hConnected Original hFiniteV hOriginal
  exact gaifmanConnected_of_surjectiveEHN
    Original Source q hq hSurj hNonempty hPath

/-- As an immediate bridge, connected positive-arity original
forbidden families have native finite JEP for their SATURATED
presentation. This is only JEP, not strong amalgamation. -/
theorem fullRangeEHNSaturation_nativeFiniteJEP_connected_positiveArity
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    GlobalNativeFiniteJEP
      (fun {W : Type} (A : Structure L W) =>
        AvoidsGlobalFunctionalEHN (FullRangeEHNSaturation F) A) := by
  exact globalNativeFiniteJEP_connected_positiveArity
    (FullRangeEHNSaturation F) hArity
    (fullRangeEHNSaturation_connectedNonempty F hConnected)

end AllThoseRamseyClasses.Lifts
