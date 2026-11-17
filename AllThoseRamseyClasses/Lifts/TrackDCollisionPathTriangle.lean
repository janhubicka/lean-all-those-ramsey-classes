import Mathlib.Tactic

/-!
# Track D: a collapsed length-three E-path creates a target triangle

A source EHN map preserves positive binary E edges and is injective
on each full irreducible source E-edge. Thus, if it identifies the
endpoints of an E-path of length three, those edges become an actual
oriented E-triangle in the target, on THREE DIFFERENT vertices.

This packages the critical collision argument in the exact printed
tuple-image-closure proof for the proposed cyclic Gamma_m family.
It does NOT claim that every pair of nonadjacent Gamma_m vertices
has a length-three path: that arithmetic fact remains a separate
general-m proof obligation. Nor does it claim that the target
triangle is FULL forbidden merely from positive E incidences:
reflection of loops, unary/D labels and absence of ternary T
via printed tuple-surjectivity remain independent premises.

The statements are representation-independent, allowing use both
for symmetric graph E and for directed binary incidence witnesses.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v

/-- A collapsed three-edge source path forces a target triangle.
The target need not be a free amalgam or have any particular
source-generated/full image factorization. -/
theorem collapsedThreeEdgePath_targetTriangle
    {V : Type u} {W : Type v}
    (E : V → V → Prop) (Et : W → W → Prop)
    (f : V → W)
    (hPres : ∀ a b : V, E a b → Et (f a) (f b))
    (hEdgeInj : ∀ a b : V, E a b → f a ≠ f b)
    {a b c d : V}
    (hab : E a b) (hbc : E b c) (hcd : E c d)
    (had : f a = f d) :
    ∃ x y z : W,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      Et x y ∧ Et y z ∧ Et z x := by
  have hZX : f c ≠ f a := by
    intro hCA
    exact (hEdgeInj c d hcd) (hCA.trans had)
  refine ⟨f a, f b, f c, hEdgeInj a b hab,
    hEdgeInj b c hbc, hZX, hPres a b hab,
    hPres b c hbc, ?_⟩
  simpa only [had] using (hPres c d hcd)

/-- No source edge can be collapsed by a map that is full on each
edge. If EVERY distinct nonadjacent pair has a length-three
source path, ANY noninjective map satisfying the two genuine
EHN edge conditions produces a target E-triangle. -/
theorem noninjectiveWithThreePath_targetTriangle
    {V : Type u} {W : Type v}
    (E : V → V → Prop) (Et : W → W → Prop)
    (f : V → W)
    (hPres : ∀ a b : V, E a b → Et (f a) (f b))
    (hEdgeInj : ∀ a b : V, E a b → f a ≠ f b)
    (hNonedgePath : ∀ a b : V, a ≠ b → ¬ E a b →
      ∃ c d : V, E a c ∧ E c d ∧ E d b)
    (hCollision : ∃ a b : V, a ≠ b ∧ f a = f b) :
    ∃ x y z : W,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      Et x y ∧ Et y z ∧ Et z x := by
  obtain ⟨a, b, hNe, hEq⟩ := hCollision
  have hNoEdge : ¬ E a b := by
    intro hab
    exact (hEdgeInj a b hab) hEq
  obtain ⟨c, d, hac, hcd, hdb⟩ :=
    hNonedgePath a b hNe hNoEdge
  exact collapsedThreeEdgePath_targetTriangle
    E Et f hPres hEdgeInj hac hcd hdb hEq

/-- Original tuple-surjectivity must be used literally: if an
old relation has no positive tuples in the source and every
target positive tuple is an image of a source positive tuple,
then the TARGET relation is also empty. This is the step which
makes the collapsed target E-triangle genuinely T-empty and
eligible for a FULL forbidden-triangle substructure. -/
theorem targetRelationEmpty_of_tupleSurjectiveSourceEmpty
    {V : Type u} {W : Type v} {I : Type}
    (R : (I → V) → Prop) (Rt : (I → W) → Prop)
    (f : V → W)
    (hEmpty : ∀ xs : I → V, ¬ R xs)
    (hTuple : ∀ ys : I → W, Rt ys →
      ∃ xs : I → V, R xs ∧ (∀ i : I, f (xs i) = ys i)) :
    ∀ ys : I → W, ¬ Rt ys := by
  intro ys hRel
  obtain ⟨xs, hR, _⟩ := hTuple ys hRel
  exact hEmpty xs hR

end AllThoseRamseyClasses.Lifts
