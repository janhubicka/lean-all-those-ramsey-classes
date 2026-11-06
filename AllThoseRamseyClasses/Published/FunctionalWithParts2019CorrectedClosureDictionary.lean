import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedSourceCertificate
import PartiteConstruction.Functional.WholeMaskRelativeClosure2019
import PartiteConstruction.Functional.WholeMaskTargetOutputHull2019

/-!
# Track C: exact functional closure equals the repaired relative U-substructure

The whole OLD complete-value decoder uses exact Option(Set) values.
If each primitive input admits at most one complete value set, it
has precisely the same closed vertex sets as the old complete-output
tuple closure predicate: every decoded defined value is an actual
complete OLD tuple, and conversely every complete OLD tuple decodes
to exactly the same whole value.

This generic statement requires value uniqueness but NO canonical
source, K-membership, fixed B-cover, U-closedness, or partite
transversality. It is valid for some-empty and repeated inputs.

Next, the verified relational 2019 dictionary equates the OLD tuple
closed-set predicate with the relative U-substructure condition when
domain-mask incidence is valid, function arities are positive, and
the U-tags are canonical.

The merged Track C source certificate supplies all these hypotheses
from ACTUAL corrected clause (4b), U-closedness, and positive arity.

Thus for an arbitrary closed corrected-(4b)-covered candidate C,
the original-language decoded partial functions are closed on Q IFF
Q is an exact U-substructure of C, even if C is U-reducible and is not
itself known to belong to H. The vertex set Q is never enlarged.
This is a GLOBAL closedness dictionary, not a claim that every
intrinsic weak test is a full OLD induced test.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- For coherent OLD whole-value data, a vertex set is closed
under the genuine Option(Set) decoder iff it is closed under
all complete output tuples, WITHOUT using a closure hull. -/
theorem wholeMaskPartialDecode_isClosed_iff_completeTuples
    (E : RelStructure (L.wholeMaskPatternLanguage Parts) V)
    (hUnique : HasUniqueWholeMaskValues E)
    (Q : Set V) :
    E.wholeMaskPartialDecode.IsClosed Q ↔
      IsClosedByWholeMaskTuples E Q := by
  classical
  constructor
  · intro hClosed p q t hOld hInputs j
    let xs : Fin (L.funcArity p.symbol) → V :=
      (fun i : Fin p.rootSize => t (Fin.castAdd q.size i)) ∘ p.argMap
    let U : Set V :=
      Set.range (fun k : Fin q.size => t (Fin.natAdd p.rootSize k))
    have hValue : HasWholeMaskValue E p.symbol xs U := by
      refine ⟨p.rootSize, p.argMap, p.onto, q, t, hOld, ?_, rfl⟩
      intro i
      rfl
    have hSome : E.wholeMaskPartialDecode.func p.symbol xs = some U :=
      (E.wholeMaskPartialDecode_func_some_iff
        p.symbol xs (hUnique p.symbol xs) U).mpr hValue
    have hXsQ : ∀ i, xs i ∈ Q := by
      intro i
      exact hInputs (p.argMap i)
    exact hClosed p.symbol xs U hXsQ hSome ⟨j, rfl⟩
  · intro hTuples F xs U hInputs hSome
    have hValue : HasWholeMaskValue E F xs U :=
      (E.wholeMaskPartialDecode_func_some_iff
        F xs (hUnique F xs) U).mp hSome
    obtain ⟨m, r, hr, q, t, hOld, hArgs, hU⟩ := hValue
    have hRootQ : ∀ i : Fin m,
        t (Fin.castAdd q.size i) ∈ Q := by
      intro i
      obtain ⟨j, hj⟩ := hr i
      have hjQ : xs j ∈ Q := hInputs j
      rw [hArgs j, hj] at hjQ
      exact hjQ
    have hOutputQ : ∀ j : Fin q.size,
        t (Fin.natAdd m j) ∈ Q :=
      hTuples ⟨F, m, r, hr⟩ q t hOld hRootQ
    intro y hy
    have hyOut : y ∈ Set.range (fun j : Fin q.size =>
        t (Fin.natAdd m j)) := by
      rw [hU] at hy
      exact hy
    obtain ⟨j, hj⟩ := hyOut
    exact hj ▸ hOutputQ j

/-- Source-side global normalization: under corrected (4b),
a set Q is closed under the decoded genuine partial functions
in the auxiliary part-labelled language iff Q is a U-substructure
of C in the exact tagged 2019 closure language.

Unlike the local-completion hypotheses, this equivalence concerns
only the vertices already in C, and is true for reducible C. -/
theorem genuineTagged2019_correctedCovered_closed_iff_Usubstructure
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (Q : Set V) :
    (wholeMaskTagReduct C).wholeMaskPartialDecode.IsClosed Q ↔
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts) C Q := by
  classical
  let E := wholeMaskTagReduct C
  let cert := genuineTagged2019_sourceCertificate_of_correctedCovered
    H C hClosed hCovered hPos
  have hFirst :
      E.wholeMaskPartialDecode.IsClosed Q ↔
        IsClosedByWholeMaskTuples E Q :=
    wholeMaskPartialDecode_isClosed_iff_completeTuples
      E cert.complete_values_unique Q
  have hSecond :
      IsClosedByWholeMaskTuples E Q ↔
        IsUSubstructure
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (wholeMaskTagExpansion E) Q :=
    isClosedByWholeMaskTuples_iff_Usubstructure
      E cert.value_domains_valid (hPos.withParts) Q
  have hCanonical : C = wholeMaskTagExpansion E :=
    cert.tag_normal.eqCanonical
  rw [hCanonical]
  exact hFirst.trans hSecond

/-- The same exact closure dictionary in the ORIGINAL genuine
partial-function language, rather than the unary-part-expanded
auxiliary language. No function domains or fibres are modified
when forgetting the unary vertex-part predicates. -/
theorem genuineTagged2019_originalDecoded_closed_iff_Usubstructure
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (Q : Set V) :
    (wholeMaskOriginalDecode C).IsClosed Q ↔
      IsUSubstructure
        ((L.withParts Parts).wholeMaskClosureRules Parts) C Q := by
  have hOriginal :
      (wholeMaskOriginalDecode C).IsClosed Q ↔
        (wholeMaskTagReduct C).wholeMaskPartialDecode.IsClosed Q := by
    constructor
    · intro h F xs U hx hValue
      exact h F.down xs U hx hValue
    · intro h F xs U hx hValue
      exact h (ULift.up F) xs U hx hValue
  exact hOriginal.trans
    (genuineTagged2019_correctedCovered_closed_iff_Usubstructure
      H C hClosed hCovered hPos Q)

/-- The function-language version of the 2019 induced-closed repair:
on an arbitrary EXACT vertex subset Q of a U-closed, corrected-(4b)
candidate C, genuine decoded function-closedness is equivalent to
the induced tagged structure C|Q itself being U-CLOSED.

There is no requirement that Q be U-irreducible, or that C be an H
member. No closure hull of Q is substituted and no new vertices
are added. This is the exact bridge to the published U-closed
substructure convention for genuine functions. -/
theorem genuineTagged2019_originalDecoded_closed_iff_induced_UClosed
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (Q : Set V) :
    (wholeMaskOriginalDecode C).IsClosed Q ↔
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce Q) := by
  exact (genuineTagged2019_originalDecoded_closed_iff_Usubstructure
      H C hClosed hCovered hPos Q).trans
    (hClosed.induce_iff_USubstructure Q).symm

/-- Equality of the same EXACT closure predicate on all subsets:
a genuine functional subset is a substructure precisely when
its tagged induced OLD image is an admissible U-closed test.
This statement has the appropriate local-finiteness quantifiers:
it does NOT range over arbitrary nonclosed intrinsic weak tests. -/
theorem genuineTagged2019_correctedCovered_closedSets_equal
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity) :
    {Q : Set V | (wholeMaskOriginalDecode C).IsClosed Q} =
      {Q : Set V |
        IsUClosed
          ((L.withParts Parts).wholeMaskClosureRules Parts)
          (C.induce Q)} := by
  ext Q
  exact genuineTagged2019_originalDecoded_closed_iff_induced_UClosed
    H C hClosed hCovered hPos Q

/-- Exact finite-cutoff test-carrier transfer. Under corrected (4b),
a predicate on Finset-indexed **genuinely function-closed**
substructures of size at most n is tested on EXACTLY the same carriers
as the corresponding predicate on induced U-closed tagged structures.

The integer n is UNCHANGED, including n=0. The predicate `Passes`
can express an actual H-completion obligation once its functional
and relational definitions have been separately related; this lemma
does not silently equate those completion predicates. -/
theorem genuineTagged2019_smallClosedTestCarriers_iff
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (n : ℕ) (Passes : Finset V → Prop) :
    (∀ S : Finset V, S.card ≤ n →
      (wholeMaskOriginalDecode C).IsClosed (↑S : Set V) →
      Passes S) ↔
    (∀ S : Finset V, S.card ≤ n →
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (↑S : Set V)) →
      Passes S) := by
  constructor
  · intro h S hSize hUClosed
    exact h S hSize
      ((genuineTagged2019_originalDecoded_closed_iff_induced_UClosed
        H C hClosed hCovered hPos (↑S : Set V)).mpr hUClosed)
  · intro h S hSize hFunctionalClosed
    exact h S hSize
      ((genuineTagged2019_originalDecoded_closed_iff_induced_UClosed
        H C hClosed hCovered hPos (↑S : Set V)).mp hFunctionalClosed)

end AllThoseRamseyClasses.Published
