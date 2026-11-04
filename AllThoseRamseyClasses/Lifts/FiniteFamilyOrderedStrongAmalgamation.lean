import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceStrongAmalgamation
import AllThoseRamseyClasses.Lifts.FiniteAmalgamBothOrders
import PartiteConstruction.Structure.Order

/-!
# Track E: full functional strong AP for freely ORDERED maximal trace age

The finite-family maximal induced-trace age has already been
kernel-verified to have genuine strong amalgamation of FULL
expanded set-valued function structures, despite not having
free amalgamation in its folded-tag language.

Given two freely linearly ordered age members Y*,Z* and
FULL ORDERED embeddings of one common ordered root X*,
forget ONLY the external order symbol. Apply genuine
unordered strong AP to the original expanded functional
reducts, producing a finite age member T and FULL old
embeddings jY,jZ with exact image-overlap equivalence.

The independent finite order theorem constructs one total
order o on the SAME T carrier strictly extending the
orders on Y and Z. The essential hypotheses are exactly
the old structural overlap equivalence and strict
monotonicity of the two original root embeddings.

Reattach that new order. The resulting side embeddings
are FULL functional ordered embeddings: they reflect the
complete old set-valued function output fibres, all added
folded component-tag predicates, and the new strict order.
The exact strong overlap law survives unchanged because
no vertices or old structural interpretations were modified.

This proves ordered STRONG AP of the freely ordered finite
maximal-trace age. It does NOT establish ordered JEP for
incompatible nullary native symbols or the complete Ramsey
class theorem. The remaining E2 difficulty is still the
corrected two-pass profiled sparse-control construction
with exact ambient-relative weak completions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Genuine STRONG amalgamation of freely ordered finite-family
maximal induced component traces, preserving every full old
relation and set-valued function fibre and all folded tags.

The common root only needs to FULLY embed into finite age
members; no separate root membership or expansion freeness
hypothesis is required. The target has exactly the same
native expanded member as the certified unordered strong
amalgam, plus one compatible external linear order.

All order-compatibility and exact intersection certificates
are constructed, not postulated. -/
theorem finiteNamedMaximalTraceAge_orderedStrongAmalgamation
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VX VY VZ : Type}
    [LinearOrder VX] [LinearOrder VY] [LinearOrder VZ]
    (X : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VX)
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VY)
    (Z : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VZ)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (hZ : IsFiniteNamedMaximalTrace Family Z)
    (fY : Structure.Embedding X.withLinearOrder Y.withLinearOrder)
    (fZ : Structure.Embedding X.withLinearOrder Z.withLinearOrder) :
    ∃ (VT : Type) (_ : Finite VT) (o : LinearOrder VT)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      ∃ (jY : Structure.Embedding Y.withLinearOrder
          (@Structure.withLinearOrder _ VT T o.toLT))
        (jZ : Structure.Embedding Z.withLinearOrder
          (@Structure.withLinearOrder _ VT T o.toLT)),
        ∀ y : VY, ∀ z : VZ,
          jY y = jZ z ↔
            ∃ x : VX, y = fY x ∧ z = fZ x := by
  classical
  have hFinY : Finite VY := hY.1
  have hFinZ : Finite VZ := hZ.1
  have hFinX : Finite VX :=
    Finite.of_injective fY fY.injective
  letI : Finite VY := hFinY
  letI : Finite VZ := hFinZ
  letI : Finite VX := hFinX
  letI : Fintype VY := Fintype.ofFinite VY
  letI : Fintype VZ := Fintype.ofFinite VZ
  letI : Fintype VX := Fintype.ofFinite VX
  obtain ⟨VT, T, hT, jY, jZ, hOverlap⟩ :=
    finiteNamedMaximalTraceAge_strongAmalgamation
      Family X Y Z hY hZ
      fY.linearOrderReduct fZ.linearOrderReduct
  have hFinT : Finite VT := hT.1
  letI : Finite VT := hFinT
  letI : Fintype VT := Fintype.ofFinite VT
  obtain ⟨o, hMonoY, hMonoZ⟩ :=
    exists_finiteAmalgamLinearOrder_extending_both
      fY fZ jY jZ
      fY.strictMono fZ.strictMono
      jY.injective jZ.injective hOverlap
  letI : LinearOrder VT := o
  have hStrictY : StrictMono jY := by
    intro a b hab
    exact hMonoY a b hab
  have hStrictZ : StrictMono jZ := by
    intro a b hab
    exact hMonoZ a b hab
  let joY : Structure.Embedding Y.withLinearOrder
      (@Structure.withLinearOrder _ VT T o.toLT) := {
    toFun := jY
    injective := jY.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R =>
          exact jY.map_rel_iff R xs
      | inr _ =>
          exact hStrictY.lt_iff_lt
    map_func := jY.map_func
  }
  let joZ : Structure.Embedding Z.withLinearOrder
      (@Structure.withLinearOrder _ VT T o.toLT) := {
    toFun := jZ
    injective := jZ.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R =>
          exact jZ.map_rel_iff R xs
      | inr _ =>
          exact hStrictZ.lt_iff_lt
    map_func := jZ.map_func
  }
  exact ⟨VT, hFinT, o, T, hT, joY, joZ, hOverlap⟩

end AllThoseRamseyClasses.Lifts
