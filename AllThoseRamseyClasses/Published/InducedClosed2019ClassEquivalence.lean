import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# Exact class-level equivalence for the proposed 2019 correction

The 2019 paper quantifies over induced substructures. The imported
partite-construction library uses abstract embedded tests.

The two descriptions of the PROPOSED COORDINATED multiamalgamation
hypotheses are genuinely equivalent for isomorphism-invariant K.
This is not definitional equality of raw Lean StructureClass
predicates: the invariant is an explicit argument.

The nontrivial directions are already individually verified:
* induced versus embedded hereditary tests (PR #101);
* exact induced versus abstract closed map/membership/weak-completion
  predicates, including preservation of the SAME cutoff n(B,C0) (#104);
* induced class -> abstract class (#103).

The present two-way class theorem rules out a remaining semantic
mismatch, but says nothing about whether either class has the
Ramsey property. No positive general Theorem 2.18 is claimed.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Faithful corrected Definition 2.17 agrees with the closed-test
working class in the pinned library for genuine isomorphism-closed
classes K. Every small original induced weak test remains tested. -/
theorem coordinated2019_class_iff_abstract
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hIso : IsomorphismClosed2019 K) :
    InducedClosed2019MultiamalgamationClass R K rules ↔
      ClosedUMultiamalgamationClass R K rules := by
  constructor
  · intro h
    exact coordinated2019_to_abstract_closed_class
      R K rules h hIso
  · intro h
    refine {
      subset := h.subset
      finite := h.finite
      closed := h.closed
      hereditary := ?_
      strong := h.strong
      localCompletion := ?_
    }
    · intro X A hA S hS
      exact h.hereditary (A.induce S) A hA hS (inclusion A S)
    · intro X Y hFiniteX hFiniteY B C0 hB hC0
      obtain ⟨n, hn⟩ := h.localCompletion B C0 hB hC0
      exact ⟨n, (inducedClosedLocalCompletion_iff_abstract_2019
        (K := K) (rules := rules) (B := B) (C0 := C0)
        (n := n) hIso).mpr hn⟩

/-- The proposed 2019 multiamalgamation CLASS assumptions, with
explicit isomorphism invariance, can be used in the library and
recovered from it without changing the mathematics of the paper.
This does NOT assert the general Ramsey theorem. -/
theorem coordinated2019_isClass_iff_abstract
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) :
    IsCoordinated2019MultiamalgamationClass R K rules ↔
      (IsomorphismClosed2019 K ∧
        ClosedUMultiamalgamationClass R K rules) := by
  constructor
  · intro h
    exact ⟨h.iso, h.toAbstract⟩
  · intro h
    exact ⟨(coordinated2019_class_iff_abstract R K rules h.1).mpr h.2,
      h.1⟩

end AllThoseRamseyClasses.Published
