import AllThoseRamseyClasses.Published.TrackENativeIrreducibleClosedCover
import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-!
# Track E: transfer a native irreducible closed cover to a tagged U-cover

The final two-pass 2019 witness is a relational tagged structure, while
the endpoint asks for protection of full irreducible *native functional*
copies. The obstacle is not Gaifman completeness: a functional
irreducible structure can have an incomplete relational Gaifman graph.

This theorem isolates the exact and sufficient cross-language properties.
For an actual tagged U-closed structure C and a native functional structure
A ON THE SAME VERTEX CARRIER, suppose:
* every relatively U-closed vertex subset of C is function-closed in A;
* whenever every C-relation tuple is on one side of a two-set cover,
  every primitive A-relation tuple and every A-function incidence is
  also supported entirely on one side.

Then genuine native irreducibility of A forces intrinsic
U-irreducibility of C. The proof invokes the already verified
native free-amalgam closed-cover theorem, not an invented graph clique.

The premises remain explicit. This does NOT assert they hold in an
arbitrary noncanonical tagged target; for the final protected 2019 target
they must be supplied by the independent exact closure dictionary
and complete whole-value side-localization lemmas.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {RL : RelLanguage.{w}} {V : Type v}

/-- Sufficient *same-vertex* criterion for U-irreducibility of a tagged
relational structure, using true native free-amalgamation irreducibility.
No assumption of ordinary relational irreducibility is made. -/
theorem nativeIrreducible_implies_uIrreducible_of_sideTransfer
    (rules : ClosureDescription RL)
    (C : RelStructure RL V) (A : Structure L V)
    (hUClosed : IsUClosed rules C)
    (hNativeIrred : A.Irreducible)
    (hRelativeClosed :
      ∀ S : Set V, IsUSubstructure rules C S → A.IsClosed S)
    (hLocalize :
      ∀ (S T : Set V),
        (∀ (R : RL.Symbol) (xs : Fin (RL.arity R) → V),
          C.rel R xs →
            (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T)) →
        (∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
          A.rel R xs →
            (∀ i, xs i ∈ S) ∨ (∀ i, xs i ∈ T)) ∧
        (∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
          (y : V), y ∈ A.func F xs →
            ((∀ i, xs i ∈ S) ∧ y ∈ S) ∨
            ((∀ i, xs i ∈ T) ∧ y ∈ T))) :
    IsUIrreducible rules C := by
  apply hUClosed.uIrreducible_of_closed_cover
  intro S T hUS hUT hCover hTuple
  obtain ⟨hRel, hFunc⟩ := hLocalize S T hTuple
  exact nativeIrreducible_closedCover A hNativeIrred S T
    (hRelativeClosed S hUS)
    (hRelativeClosed T hUT)
    hCover hRel hFunc

end AllThoseRamseyClasses.Published
