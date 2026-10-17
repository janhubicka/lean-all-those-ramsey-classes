import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam
import AllThoseRamseyClasses.Lifts.FiniteFunctionalExpansionFibres
import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig
import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguage
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Sets

/-!
# Finite tagged folded lifts for ALL closed-root components of one finite source

The printed 2019 minimal-separator piece index causes the difficult
multicomponent Claim 2. For one fixed finite forbidden source,
a DIFFERENT auxiliary lift can instead name each actual pair
  (function-closed vertex cut R, component C of Source minus R),
without requiring R to be inclusion-minimal.

For finite Source, this tag type is FINITE, even if the original
language has infinitely many old relation/function symbols.
Each tag determines an exact complete functional rooted pattern on
R ∪ C, with a canonical noncomputable enumeration of the entire root
R. No new vertex or partial function is introduced.

The auxiliary canonical relation records a weak EHN realization of
that actual rooted pattern on an arbitrary target tuple, ALLOWING
coinciding root images. Its old shadow is literally unchanged;
the finite tag type makes the possible expansion fibre of every
finite old shadow finite.

This is a fully explicit finite-index alternative for ONE NAMED
finite source. Extending it equivariantly to a finite family of
isomorphism types and proving amalgamation for its maximal lifted
class are independent later tasks. Regular INFINITE forbidden
families are not covered by this finite-tag construction.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- A genuine induced component of ONE fixed functional source
above an arbitrary function-closed root R. Minimality of R is
deliberately NOT imposed. -/
structure ClosedComponentTag (Source : Structure L V) where
  cut : Set V
  closed : Source.IsClosed cut
  chosen : {x : V // x ∉ cut}

/-- Over a fixed finite source there are only finitely many
closed vertex sets and chosen surviving vertices. The closure
condition is Prop and does not create new tags. -/
theorem closedComponentTag_finite
    [Finite V] (Source : Structure L V) :
    Finite (ClosedComponentTag Source) := by
  classical
  letI : Finite (Set V) := inferInstance
  letI (R : Set V) : Finite {x : V // x ∉ R} :=
    Finite.of_injective
      (fun x : {x : V // x ∉ R} => x.1)
      (by intro a b h; exact Subtype.ext h)
  let encode : ClosedComponentTag Source →
      (Σ R : Set V, {x : V // x ∉ R}) :=
    fun t => ⟨t.cut, t.chosen⟩
  apply Finite.of_injective encode
  intro a b hab
  cases a with
  | mk Ra hRa xa =>
    cases b with
    | mk Rb hRb xb =>
      dsimp [encode] at hab
      cases hab
      rfl

noncomputable instance (Source : Structure L V) [Finite V] :
    Finite (ClosedComponentTag Source) :=
  closedComponentTag_finite Source

/-- Exact width: cardinality of the FULL native function-closed
root, not a boundary subset or closure hull. -/
noncomputable def ClosedComponentTag.width
    {Source : Structure L V}
    (t : ClosedComponentTag Source) : ℕ :=
  Nat.card t.cut

/-- Enumerate the entire cut exactly once. Repeated images of
distinct root vertices are allowed only later, in weak maps
into a target witness. -/
noncomputable def ClosedComponentTag.enumeration
    {Source : Structure L V}
    (t : ClosedComponentTag Source)
    [Finite V] :
    Fin t.width ≃ t.cut := by
  letI : Finite t.cut :=
    Finite.of_injective
      (fun x : t.cut => x.1)
      (by intro a b h; exact Subtype.ext h)
  exact (Finite.equivFin t.cut).symm

/-- The exact actual native functional rooted component pattern.
Its source root tuple is injective and covers WHOLE cut R; no
minimal separating cut hypothesis is needed. -/
noncomputable def ClosedComponentTag.rootedPattern
    {Source : Structure L V}
    [Finite V]
    (t : ClosedComponentTag Source) :
    FunctionalRootedPattern L t.width where
  Carrier := functionalComponentUnion Source t.cut t.chosen
  str := functionalComponentInduce Source
    t.cut t.closed t.chosen
  root := fun i =>
    ⟨(t.enumeration i).1, Or.inl (t.enumeration i).2⟩
  root_injective := by
    intro i j h
    have hval :
        (t.enumeration i).1 = (t.enumeration j).1 :=
      congrArg Subtype.val h
    exact t.enumeration.injective (Subtype.ext hval)

/-- Extend any target OLD functional structure by one tag relation
for EACH genuine closed-root component of the fixed finite source.
Membership records a weak rooted EHN realization and does NOT
filter for injective image coordinates. -/
noncomputable def allClosedComponentFoldedLift
    [Finite V]
    (Source : Structure L V)
    {W : Type v} (A : Structure L W) :
    Structure
      (functionalLiftLanguageBig L
        (ClosedComponentTag Source)
        (fun t => t.width)) W :=
  functionalWithExtraBig L
    (ClosedComponentTag Source)
    (fun t => t.width) A
    (fun t xs =>
      FunctionalRootRealization t.rootedPattern A xs)

/-- The entire old relation/function structure and all partial
function-value fibres are preserved LITERALLY, not merely
embedded in the new tagged expansion. -/
@[simp] theorem allClosedComponentFoldedLift_shadow
    [Finite V]
    (Source : Structure L V)
    {W : Type v} (A : Structure L W) :
    functionalShadowBig L
      (ClosedComponentTag Source)
      (fun t => t.width)
      (allClosedComponentFoldedLift Source A) = A :=
  functionalShadowBig_withExtra L
    (ClosedComponentTag Source)
    (fun t => t.width) A _

/-- Exact new relation semantics: a tagged tuple is present iff
the genuine native component piece weakly realizes the tuple,
including when root images collide. -/
theorem allClosedComponentFoldedLift_relation_iff
    [Finite V]
    (Source : Structure L V)
    {W : Type v} (A : Structure L W)
    (t : ClosedComponentTag Source)
    (xs : Fin t.width → W) :
    (allClosedComponentFoldedLift Source A).rel (.inr t) xs ↔
      FunctionalRootRealization t.rootedPattern A xs := by
  rfl

/-- Any EHN weak realization of a TRUE tagged native component
induces its folded relation on its actual root-image tuple.
NO root-image injectivity is needed. -/
theorem allClosedComponentFoldedRelation_of_weak
    [Finite V]
    (Source : Structure L V)
    {W : Type v} (A : Structure L W)
    (t : ClosedComponentTag Source)
    (f : t.rootedPattern.Carrier → W)
    (hf : t.rootedPattern.str.IsEHNHomomorphismEmbedding A f) :
    (allClosedComponentFoldedLift Source A).rel
      (.inr t) (fun i => f (t.rootedPattern.root i)) := by
  apply (allClosedComponentFoldedLift_relation_iff
    Source A t (fun i => f (t.rootedPattern.root i))).mpr
  exact ⟨f, hf, fun _ => rfl⟩

/-- Conversely the extra relation provides a weak realization
of the SAME true component piece, with no class quotient and
exactly the specified, possibly colliding, full root images. -/
theorem allClosedComponentFoldedRelation_witness
    [Finite V]
    (Source : Structure L V)
    {W : Type v} (A : Structure L W)
    (t : ClosedComponentTag Source)
    (xs : Fin t.width → W)
    (h : (allClosedComponentFoldedLift Source A).rel (.inr t) xs) :
    ∃ f : t.rootedPattern.Carrier → W,
      t.rootedPattern.str.IsEHNHomomorphismEmbedding A f ∧
      ∀ i : Fin t.width, f (t.rootedPattern.root i) = xs i :=
  (allClosedComponentFoldedLift_relation_iff
    Source A t xs).mp h

/-- The auxiliary tag language has a FINITE new relation-symbol
type over one named finite source, so all expansions above any
fixed finite old functional shadow form a finite fibre.
No old relation or function symbols need to be finite. -/
theorem allClosedComponentFoldedLift_finiteShadowFibre
    [Finite V]
    (Source : Structure L V)
    {W : Type v} [Finite W]
    (A : Structure L W) :
    Finite
      (FixedFunctionalShadowExpansions L
        (ClosedComponentTag Source)
        (fun t => t.width) A) :=
  fixedFunctionalShadowExpansions_finite
    L (ClosedComponentTag Source)
    (fun t => t.width) A

end AllThoseRamseyClasses.Lifts
