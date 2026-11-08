import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedIntrinsicLocalTransfer
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track C: a corrected native local CLASS axiom testing only closed substructures

The survey's printed local-finiteness condition tests genuine FUNCTION
substructures, not arbitrary intrinsic weak restrictions. A genuine
partial-function substructure must be closed under all defined
operation values (and retain source-defined empty values).

The 2019 corrected tagged relative local axiom, by contrast, requires
a completion implication whose antecedent tests EVERY exact ambient
OLD-induced weak subset S, including nonclosed S with persistent
domain bits. The already verified Track C bridge converts each of
those ambient H completions into a genuine source-defined partial
functional map with full protection of the canonical ambient closed
U-irreducible copies.

Here we define a corrected native class-level local implication
that tests only genuinely FUNCTION-CLOSED subsets S. It retains the
same B, C0, n, corrected (4b), control map and copywise conclusion as
the relational theorem. This closed-only assumption is SUFFICIENT for
the original full part-preserving functional Ramsey theorem, because
the stronger all-weak antecedent entails the closed-only antecedent.

The completion map notion remains the checked canonical-protected
functional map. No claim is made that the local class hypothesis
is equivalent to every reading of the survey's printed definition,
or that full functional embeddings of nonclosed S are supplied.

Closedness is the only hypothesis needed to identify the genuine
full induced partial-function source with the whole-fibre weak source
on precisely S. The comparison handles undefined vs defined-empty.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V W Z : Type w}

/-- If S is closed under genuine partial-function values, the
complete-fibre weak restriction and the genuine induced closed
substructure have identical Option(Set) values (including none
and some empty), at EVERY primitive function input. -/
theorem wholeWeakInduce_func_eq_induceClosed_of_isClosed
    (A : PartialSetStructure L V)
    (S : Set V) (hS : A.IsClosed S)
    (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → S) :
    (wholeWeakInduce A S).func F xs =
      (A.induceClosed S hS).func F xs := by
  classical
  change wholeWeakValue S (A.func F (Subtype.val ∘ xs)) =
    (A.func F (Subtype.val ∘ xs)).map
      (fun T => {y : S | y.1 ∈ T})
  cases hv : A.func F (Subtype.val ∘ xs) with
  | none =>
      rfl
  | some T =>
      have hT : T ⊆ S :=
        hS F (Subtype.val ∘ xs) T (fun i => (xs i).2) hv
      simpa only [hv, Option.map_some] using
        wholeWeakValue_of_subset S T hT

/-- For an actual closed functional S, a canonical-protected
genuine H completion of its whole-weak restriction is an original
source-defined partial-function completion of its TRUE induced
functional substructure. Its H target, part labels and map are
literally unchanged. -/
theorem intrinsicCanonicalProtected_closed_is_genuinePartial
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (partC : V → Parts)
    (S : Set V)
    (hS : (wholeMaskOriginalDecode C).IsClosed S)
    (hNative : HasGenuineIntrinsicWeakCanonicalProtectedCompletion
      H C partC S) :
    ∃ (X : Type w) (_ : Finite X)
      (Target : PartialSetStructure L X) (targetPart : X → Parts),
      H Target targetPart ∧ FibreTransversal Target targetPart ∧
      ∃ (f : S → X),
        IsOriginalPartialHomomorphism
          ((wholeMaskOriginalDecode C).induceClosed S hS)
          Target f ∧
        (∀ x : S, targetPart (f x) = partC x.1) := by
  obtain ⟨X, hFinite, Target, targetPart, hH, hTr,
    f, hPartial, hPart, _⟩ := hNative
  refine ⟨X, hFinite, Target, targetPart, hH, hTr, f, ?_, hPart⟩
  constructor
  · exact hPartial.1
  · intro F xs U hValue
    have hWeak :
        (wholeWeakInduce (wholeMaskOriginalDecode C) S).func F xs =
          ((wholeMaskOriginalDecode C).induceClosed S hS).func F xs :=
      wholeWeakInduce_func_eq_induceClosed_of_isClosed
        (wholeMaskOriginalDecode C) S hS F xs
    exact hPartial.2 F xs U (hWeak.trans hValue)

/-- A corrected functional CLASS-local axiom with genuine closed
small source carriers. The completion target remains a genuine
H-member and every canonical ambient closed U-irreducible copy
is fully protected by the exact same local map.

The OUTER hypotheses and B-copywise conclusion are exactly those of
the checked corrected relational (4c) axiom; this definition does
NOT claim the unmodified survey defn:locfin is equivalent to it. -/
def GenuinePartiteIntrinsicClosedCanonicalProtectedLocalCompletionAt
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ) : Prop :=
  ∀ {X : Type w} [Finite X]
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (hClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hControl : C0.Irreducible ∧ ∃ p : X → Z,
      IsInducedClosedUHomomorphismEmbedding
        ((L.withParts Parts).wholeMaskClosureRules Parts) C C0 p)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C),
    (∀ S : Finset X, S.card ≤ n →
      (wholeMaskOriginalDecode C).IsClosed (↑S : Set X) →
      HasGenuineIntrinsicWeakCanonicalProtectedCompletion
        H C (genuineTagged2019_correctedCoveredPart
          H C hClosed hCovered) (↑S : Set X)) →
    HasCopywiseCompletion (canonicalGenuineTagged2019Class H) B C

/-- Closed-substructure local implications are sufficient for the
corrected all-weak local implication, with the SAME cutoff n:
the all-weak functional small-test antecedent is strictly stronger.
No monotonicity trick or increase of n is needed. -/
theorem genuinePartite2019_allWeakLocal_of_closedNativeLocal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) W)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (n : ℕ)
    (hLocal :
      GenuinePartiteIntrinsicClosedCanonicalProtectedLocalCompletionAt
        H B C0 n) :
    GenuinePartiteIntrinsicCanonicalProtectedLocalCompletionAt
      H B C0 n := by
  intro X hFinite C hClosed hControl hCovered hAllWeak
  apply hLocal C hClosed hControl hCovered
  intro S hSize _
  exact hAllWeak S hSize

/-- In the ORIGINAL genuine partial Option(Set) functional language,
the corrected CLOSED-only local canonical-protected class condition
is sufficient for the full part-preserving Ramsey property.
All ambient Ramsey, hereditary, strong-amalgamation, isomorphism
and positive-input-arity assumptions remain explicitly present.
No claim that this hypothesis equals the survey's unmodified
`defn:locfin` is made. -/
theorem genuinePartite2019_ramsey_of_closedNativeCanonicalProtectedLocal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (R : StructureClass
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class H E → R E)
    (hPos : L.PositiveFuncArity)
    (hHer : GenuinePartiteClosedHereditary2019 H)
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hLocalClosed : ∀ {X Y : Type w} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class H B → R C0 →
      ∃ n : ℕ,
        GenuinePartiteIntrinsicClosedCanonicalProtectedLocalCompletionAt
          H B C0 n) :
    GenuinePartite2019FiniteRamsey H := by
  apply genuinePartite2019_ramsey_of_intrinsicCanonicalProtectedLocalCompletion
    H R hR hRIrred hSub hPos hHer hStrong hIso
  intro X Y hX hY B C0 hB hC0
  obtain ⟨n, hLocal⟩ := hLocalClosed B C0 hB hC0
  exact ⟨n,
    genuinePartite2019_allWeakLocal_of_closedNativeLocal
      H B C0 n hLocal⟩

end AllThoseRamseyClasses.Published
