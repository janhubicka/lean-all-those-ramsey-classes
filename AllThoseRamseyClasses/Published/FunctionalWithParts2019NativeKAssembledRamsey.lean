import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKIsoClosure
import AllThoseRamseyClasses.Published.FunctionalWithParts2019AssembledRamsey

/-!
# Track B: conditional native-K version of the corrected 2019 Ramsey theorem

The faithful original partial-function class H_K consists of actual
part-transversal native K-systems interpreted as genuine Option(Set)
structures on the SAME carriers, with their true vertex parts.
The canonical relational K_H class names each part predicate and
every complete OLD domain/output mask and fresh U-root closure tag.

Under the native FreeAmalgamationClass K axiom, the earlier Track B
results derive genuine H_K closed heredity, finite strong
amalgamation and isomorphism closure of canonical tagged K_H.
Thus the already verified assembled corrected 2019 Ramsey theorem
can be specialized to H_K directly: no unrelated functional H class
or additional H_K class-property assumptions are needed.

Exactly two INDEPENDENT families of hypotheses remain:

* choose a genuine irreducible relational Ramsey host R and prove
  every canonical tagged K_H-member is also an R-member;
* prove the corrected ambient-RELATIVE local K_H completion axiom
  with a uniform finite cutoff n(B,C0), for EVERY ambient
  R-controlled sparse source C satisfying the original
  corrected quantified local-completion premises, and for ALL
  its exact induced weak subsets of size <= n.

Source-stage weak closure/rank dictionaries DO NOT discharge that
second hypothesis. In particular no intrinsic weak positive
homomorphism is declared to preserve all ambient OLD domain bits.
This endpoint is conditional on the precise global 2019 local
assumption, not a claimed solution of Track C.

No intermediate relational witness is replaced by a native power;
the two-pass 2019 sparsening theorem supplies the Ramsey conclusion
as already formally verified, once its exact class hypotheses hold.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Source-class specialization of the VERIFIED corrected 2019
partite sparse Ramsey theorem for a native functional
FreeAmalgamationClass K, using EXACT faithful H_K and canonical
full-root tagged K_H.

Every H_K closed-heredity, strong amalgamation and isomorphism
hypothesis is supplied by the prior native-to-genuine Track B
bridges, not postulated afresh.

The relational Ramsey host and subset-inclusion conditions and
the CORRECTED ambient-relative local-completion axiom on every
small exact weak induced test remain explicit. The cutoff n(B,C0)
is unchanged; no false intrinsic/ambient weak equivalence or
strict functional B-tree completion is inferred. -/
theorem nativeKFaithful2019_ramsey_of_relative_local_data
    (K : Structure.StructureClass.{u,v} (L := L))
    (hFree : Structure.FreeAmalgamationClass K)
    (R : StructureClass.{max u v,v}
      (L := (L.withParts Parts).wholeMaskTagLanguage Parts))
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      R E → E.Irreducible)
    (hSub : ∀ {X : Type v}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X),
      canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) E → R E)
    (hPos : L.PositiveFuncArity)
    (hLocal : ∀ {X Y : Type v} [Finite X] [Finite Y]
      (B : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
      (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) B →
      R C0 →
      ∃ n : ℕ, GenuinePartiteTagged2019LocalCompletionAt
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)
        B C0 n) :
    GenuinePartite2019FiniteRamsey
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) := by
  let H : GenuinePartite2019Class.{u,v,v}
      (L := L) (Parts := Parts) :=
    nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K
  have hHer : GenuinePartiteClosedHereditary2019 H :=
    nativeKFaithfulH_closedHereditary_of_freeAmalgamationClass
      (Parts := Parts) K hFree
  have hStrong : GenuinePartiteStrongAmalgamation2019 H :=
    nativeKFaithfulH_strongAmalgamation_of_free
      (Parts := Parts) K hFree
  have hIso : IsomorphismClosed2019
      (canonicalGenuineTagged2019Class H) :=
    nativeKCanonicalTagged2019_isomorphismClosed_of_free
      (Parts := Parts) K hFree
  apply genuinePartite2019_ramsey_of_original_class_data.{u,v,v}
    (L := L) (Parts := Parts) H R hR
  · exact hRIrred
  · exact hSub
  · exact hPos
  · exact hHer
  · exact hStrong
  · exact hIso
  · exact hLocal

end AllThoseRamseyClasses.Published
