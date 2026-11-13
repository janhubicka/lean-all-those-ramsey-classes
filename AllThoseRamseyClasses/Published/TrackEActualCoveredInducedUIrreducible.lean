import AllThoseRamseyClasses.Published.TrackEClosedNativeCoverToUIrreducible
import PartiteConstruction.Functional.TrackEFinalInducedTestLocalization2019

/-!
# Track E: native irreducible full tests are U-irreducible in the ACTUAL
# protected-B-covered final 2019 tagged witness, on exact vertex sets

The final tagged 2019 sparse Ramsey structure C is not assumed to equal
the canonical tag of its decoded functional structure. The checked
whole-mask decoder supplies a genuine native set-valued-function structure
on exactly the same vertex carrier, with complete-value witnesses.

For any exact S closed under these decoded functions, assume the full
native substructure on S is genuinely irreducible in the universal
free-amalgamation sense. Then C.induce S is intrinsically U-irreducible.

Proof: #621/#622 transfer decoded closedness and relative U-closed sides
to the actual tagged C; #634 transfers every side of an induced
tagged relation-tuple localization to a function-closed side of the
native S-structure, and makes each complete primitive function incidence
side-local. The native closed-cover theorem (#1016), packaged in #1099,
rules out any proper two-sided free cover of C.induce S.

No Gaifman-complete graph assumption, no canonically tagged E-lift, no
weak-test hull or replacement of S, no strict native mixed tree.
This is the missing geometric test-eligibility theorem; the selected
global HE upgrade and the original 2019 endgame remain distinct steps.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {P : Type w} [Fintype P]
variable {V W : Type v}

/-- For the ACTUAL final B-covered whole-mask tagged 2019 witness, every
function-closed exact S that is genuinely native-irreducible as a full
functional substructure is an intrinsically U-irreducible tagged test on
precisely S. Both structure and native test have the same original
vertex carrier S and no other vertices are introduced. -/
theorem wholeMaskCovered_inducedUIrreducible_of_nativeIrreducible
    (C : RelStructure (L.wholeMaskTagLanguage P) V)
    (Base : PartialSetStructure L W) (part : W → P)
    (hC : IsUClosed (L.wholeMaskClosureRules P) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {X : Type v}
      (Test : RelStructure (L.wholeMaskTagLanguage P) X),
      IsUClosed (L.wholeMaskClosureRules P) Test →
      IsUIrreducible (L.wholeMaskClosureRules P) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion (Base.wholeMaskPatternGraph part))))
    (S : Set V)
    (hS : ((wholeMaskTagReduct C).wholeMaskPartialDecode).IsClosed S)
    (hNativeIrred :
      (((wholeMaskTagReduct C).wholeMaskPartialDecode.collapseDomain).induce
        S ((PartialSetStructure.isClosed_iff_collapseDomain_isClosed
          (wholeMaskTagReduct C).wholeMaskPartialDecode S).mp hS)).Irreducible) :
    IsUIrreducible (L.wholeMaskClosureRules P) (C.induce S) := by
  let A : PartialSetStructure L V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  let N : Structure L V := A.collapseDomain
  have hNClosed : N.IsClosed S :=
    (A.isClosed_iff_collapseDomain_isClosed S).mp hS
  have hClosedTest :
      IsUClosed (L.wholeMaskClosureRules P) (C.induce S) :=
    wholeMaskCovered_decodedClosed_to_inducedUClosed
      C Base part hC hPos hCover S hS
  apply nativeIrreducible_implies_uIrreducible_of_sideTransfer
    (L.wholeMaskClosureRules P) (C.induce S) (N.induce S hNClosed)
    hClosedTest hNativeIrred
  · intro X hX
    exact wholeMaskCovered_inducedUSubstructure_to_nativeClosed
      C Base part hC hPos hCover S hS X hX
  · intro X Y hTuple
    constructor
    · intro R xs hRel
      exact hTuple (.inl (.inl R)) xs hRel
    · intro F xs y hy
      exact wholeMaskCovered_inducedNativeFunctionIncident_side
        C Base part hC hPos hCover S hS X Y hTuple F xs y hy

end AllThoseRamseyClasses.Published
