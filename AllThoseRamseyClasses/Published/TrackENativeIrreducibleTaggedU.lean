import AllThoseRamseyClasses.Published.TrackENativeIrreducibleClosedCover
import PartiteConstruction.Functional.NativeUClosedExactDictionary
import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-!
# Track E2: native irreducibility implies canonical singleton-pattern U-irreducibility

The corrected 2019 completion map protects U-CLOSED and U-IRREDUCIBLE
relational tests, not arbitrary ordinarily irreducible graphs. A
functional unary chain may be irreducible by closure while its old
Gaifman graph is not complete. Therefore the correct conclusion for
an intrinsically irreducible singleton-valued native structure is
intrinsic U-IRREDUCIBILITY of its canonical full-root tagged pattern
graph, not ordinary relational irreducibility.

Proof via precise closed covers:
* singleton output values imply canonical tagged U-closedness;
* the verified exact 2019 dictionary identifies every relative
  U-substructure with a native function-closed vertex subset;
* a free cover of the tagged relations keeps every original relation
  tuple and each function input/output incidence on one side;
* the native closed-cover lemma rules out proper two-sided covers;
* the verified relational U-closed-cover converse gives intrinsic
  U-irreducibility.

No closure hull is taken, no new vertices or ordering are inserted,
and all repeated or nullary function inputs are handled by their
exact equality-pattern factorization. A positive-function-arity
hypothesis is required ONLY for the native closedness dictionary.
The final B-covered sparse witness still needs an independent
canonical induced-test comparison; this theorem does not assert it.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Every finite singleton-valued native full functional irreducible
test has an intrinsically U-irreducible CANONICAL tagged equality-pattern
presentation. This is strictly weaker than ordinary relational
irreducibility and is the right closed-test predicate for the
coordinated corrected 2019 induced-closed local completion condition.

The actual tagged source is canonical here. No conclusion about
arbitrary noncanonical intermediate tagged Ramsey pictures is made. -/
theorem nativeIrreducible_canonicalSingletonTag_uIrreducible
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (hSingle : A.SingletonValued)
    (hIrred : A.Irreducible) :
    IsUIrreducible L.patternClosureRules
      (patternTagExpansion A.patternGraph) := by
  classical
  let Tag : RelStructure L.patternTag V :=
    patternTagExpansion A.patternGraph
  have hTagClosed : IsUClosed L.patternClosureRules Tag :=
    patternTagExpansion_isUClosed A hSingle
  apply hTagClosed.uIrreducible_of_closed_cover
  intro S T hUS hUT hCover hTuple
  have hS : A.IsClosed S :=
    (A.isClosed_iff_taggedPattern_isUSubstructure hPos S).mpr hUS
  have hT : A.IsClosed T :=
    (A.isClosed_iff_taggedPattern_isUSubstructure hPos T).mpr hUT
  apply nativeIrreducible_closedCover A hIrred S T hS hT hCover
  · intro R xs hRel
    exact hTuple (.inl (.inl R)) xs hRel
  · intro F xs y hy
    obtain ⟨m, r, root, hr, hInj, hFact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact xs
    let pat : Language.FunctionInputPattern L :=
      ⟨F, m, r, hr⟩
    let t : Fin (m + 1) → V := Structure.funcTuple root y
    have hArgs : root ∘ r = xs := by
      funext i
      exact (hFact i).symm
    have hOld :
        Tag.rel (.inl (.inr (.inr pat))) t := by
      change Function.Injective root ∧ y ∈ A.func F (root ∘ r)
      refine ⟨hInj, ?_⟩
      rw [hArgs]
      exact hy
    have hSingleSide
        (Q : Set V)
        (hSide : ∀ k : Fin (m + 1), t k ∈ Q) :
        (∀ i, xs i ∈ Q) ∧ y ∈ Q := by
      constructor
      · intro i
        have hi := hSide (Fin.castSucc (r i))
        have ht : t (Fin.castSucc (r i)) = root (r i) :=
          Structure.funcTuple_castSucc root y (r i)
        rw [ht] at hi
        rw [hFact i]
        exact hi
      · have hi := hSide (Fin.last m)
        have ht : t (Fin.last m) = y :=
          Structure.funcTuple_last root y
        rw [ht] at hi
        exact hi
    rcases hTuple (.inl (.inr (.inr pat))) t hOld with hLeft | hRight
    · exact Or.inl (hSingleSide S hLeft)
    · exact Or.inr (hSingleSide T hRight)

end AllThoseRamseyClasses.Published
