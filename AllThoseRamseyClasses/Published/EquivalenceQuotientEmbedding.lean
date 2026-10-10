import AllThoseRamseyClasses.Published.EquivalenceOverlapClasses

/-!
# Induced injections between E-class quotient sets

To amalgamate E, we form each side's equivalence-class set and
identify precisely those classes which come from a common
equivalence class of the root D.

A FULL embedding s : D -> Left must therefore induce an INJECTION
D/E_D -> Left/E_Left, not just a map preserving positive tuples.
The injectivity of this quotient map is the key to constructing the
joined E relation without adding forbidden pairs inside one side.

No choice of representatives, use of a closure hull, or unspecified
amalgamation oracle is hidden. The quotient-label pushout and its
side restrictions will follow in a subsequent module.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The original E equivalence relation as an explicit Setoid. -/
def pairedClassSetoid
    {V : Type} (C : RelStructure Lang V)
    (hC : pairedClass C) : Setoid V :=
  ⟨edge C .equiv, hC.equiv⟩

/-- Any full embedding of paired equivalence structures induces a
map of E-class quotient sets, respecting the ORIGINAL E relation. -/
noncomputable def pairedClassQuotientMap
    {D V : Type}
    {Root : RelStructure Lang D}
    {Side : RelStructure Lang V}
    (hRoot : pairedClass Root)
    (hSide : pairedClass Side)
    (s : Embedding Root Side) :
    Quotient (pairedClassSetoid Root hRoot) →
      Quotient (pairedClassSetoid Side hSide) :=
  Quotient.lift
    (fun d : D =>
      Quotient.mk (pairedClassSetoid Side hSide) (s d))
    (by
      intro a b hab
      apply Quotient.sound
      exact (equivalence_embedding_iff s a b).mpr hab)

/-- The induced class map is INJECTIVE: two distinct root
E-classes cannot merge within an induced side embedding. -/
theorem pairedClassQuotientMap_injective
    {D V : Type}
    {Root : RelStructure Lang D}
    {Side : RelStructure Lang V}
    (hRoot : pairedClass Root)
    (hSide : pairedClass Side)
    (s : Embedding Root Side) :
    Function.Injective (pairedClassQuotientMap hRoot hSide s) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ x =>
    induction b using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      apply (equivalence_embedding_iff s x y).mp
      have he :
          Quotient.mk (pairedClassSetoid Side hSide) (s x) =
            Quotient.mk (pairedClassSetoid Side hSide) (s y) := hab
      exact Quotient.exact he

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
