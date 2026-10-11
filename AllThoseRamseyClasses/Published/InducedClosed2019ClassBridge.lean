import AllThoseRamseyClasses.Published.InducedClosed2019MainContract
import AllThoseRamseyClasses.Published.InducedClosed2019HereditaryBridge

/-!
# Coordinated 2019 multiamalgamation: exact paper class to library class

The *proposed corrected* 2019 Definitions 2.15/2.17 are expressed by
\`InducedClosed2019MultiamalgamationClass\`: all tests are actual
induced substructures of the original source; nonclosed exact weak
n-vertex substructures are STILL included in (4c).

The reusable \`partite-construction\` proof interface instead uses
abstract embedded CLOSED tests for maps and membership. The
paper-faithful assumptions imply that interface at the SAME
cutoff n(B,C0), once the usually implicit isomorphism invariance
of the mathematical class K is made explicit. This is a one-way
implication, not an assertion that the raw predicates coincide.

The core ingredients are:
* induced closed hereditariness -> embedded closed hereditariness
  for an isomorphism-closed class (independently audited);
* induced local-completion implication -> abstract closed-test
  implication, with exactly the original weak test cardinal bound
  (independently audited in InducedClosedLogicalDirection);
* every remaining class axiom is literally identical.

No sparse/Picture witness is constructed by this file, and neither
the library's unrestricted abstract theorem nor the proposed
corrected Theorem 2.18 is asserted to hold.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The formalization of a genuine 2019 *class* includes its
usually tacit invariance under isomorphism. Its mathematical
closed hereditary tests remain INDUCED, not replaced by
embedded-test quantifiers. -/
structure IsCoordinated2019MultiamalgamationClass
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop where
  induced : InducedClosed2019MultiamalgamationClass R K rules
  iso : IsomorphismClosed2019 K

/-- Exactly one-way semantic transfer: the proposed corrected paper
class hypothesis is strong enough for the abstract closed-test
working hypotheses in the pinned partite-construction library.
The local cutoff n(B,C0) is unchanged. -/
theorem coordinated2019_to_abstract_closed_class
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (h : InducedClosed2019MultiamalgamationClass R K rules)
    (hIso : IsomorphismClosed2019 K) :
    ClosedUMultiamalgamationClass R K rules := by
  refine {
    subset := h.subset
    finite := h.finite
    closed := h.closed
    hereditary := embeddedClosedHereditary_of_induced h.hereditary hIso
    strong := h.strong
    localCompletion := ?_
  }
  intro X Y B C0 hB hC0
  obtain ⟨n, hn⟩ := h.localCompletion B C0 hB hC0
  exact ⟨n, InducedClosedULocalCompletionAt.toAbstractClosed hn⟩

/-- The same bridge packaged with the actual paper-style class
assumption rather than passing its isomorphism-invariance separately. -/
theorem IsCoordinated2019MultiamalgamationClass.toAbstract
    {R K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    (h : IsCoordinated2019MultiamalgamationClass R K rules) :
    ClosedUMultiamalgamationClass R K rules :=
  coordinated2019_to_abstract_closed_class R K rules h.induced h.iso

/-- Library-level GENERAL Ramsey theorem target. It is a proposition,
NOT a theorem proved by this file or the pinned dependency. -/
def AbstractClosed2019Theorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible) →
    ClosedUMultiamalgamationClass R K rules →
    FiniteRamseyClass K

/-- The mathematical 2019 Theorem 2.18 after the coordinated map
and (4b) correction, and after spelling out that K is a class
closed under isomorphism. Again, this is a TARGET proposition. -/
def Coordinated2019Theorem218Target : Prop :=
  ∀ (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L),
    FiniteRamseyClass R →
    (∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible) →
    IsCoordinated2019MultiamalgamationClass R K rules →
    FiniteRamseyClass K

/-- Conditional reduction from the hypothetical complete abstract
closed-test theorem to the corrected 2019 theorem. No missing
constructor is hidden: the ENTIRE abstract theorem is an explicit
hypothesis. The positive Ramsey theorem remains open. -/
theorem coordinated2019_target_of_abstract_target
    (hAbstract : AbstractClosed2019Theorem218Target (L := L)) :
    Coordinated2019Theorem218Target (L := L) := by
  intro R K rules hRamsey hIrred hK
  exact hAbstract R K rules hRamsey hIrred hK.toAbstract

end AllThoseRamseyClasses.Published
