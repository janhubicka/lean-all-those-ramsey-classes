import AllThoseRamseyClasses.Lifts.ForbiddenPieceClosedRoots
import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig
import AllThoseRamseyClasses.Lifts.FixedRootCanonicalWitness

/-!
# Global width-indexed functional forbidden-piece classes and lift

The 2019 construction adds ONE relation for each class of genuine
finite forbidden pieces, under equality of incompatibility profiles.
Tests range over ALL rooted structures compatible with the given
full root, not merely other forbidden pieces.

A root chart explicitly stores its entire induced FUNCTIONAL
structure on the ordered standard carrier Fin n and an extension
by a full root embedding. Two charts can be freely glued only when
these structures are EQUAL, not merely when their widths agree.

This first global index is universe-zero on the finite source carriers (Type), which permits an exact Fin n full root in the existing FunctionalRootExtension API. This does not assert a universe-polymorphic correspondence with every possible higher-universe carrier; that transfer needs an explicit renaming lemma.

This handles pieces belonging to different full root structures:
their incompatibility profiles are compared as subsets of the SAME
type of all rooted charts at width n. Hence the setoid does not
silently identify root structures, and the global quotient has one
new symbol for each positive-width class.

The symbol type may live in a HIGHER universe, so we use the
universe-polymorphic functional lift. Every original function
symbol and its entire interpretation are preserved exactly.

The remaining theorem connecting this quotient to the fixed-root
piece-setoid is separate. Its proof must use existence of a
forbidden complementary test to rule out accidental equivalences
between distinct root structures.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

/-- One rooted functional structure with an exact complete induced
root structure on its ordered Fin n root. -/
structure FunctionalRootChart (L : Language.{u}) (n : ℕ) where
  root : Structure L (Fin n)
  ext : FunctionalRootExtension.{u,0} root

/-- The underlying native rooted pattern, with ordered roots
given by the full embedding of the standard root. -/
def FunctionalRootChart.pattern
    {L : Language.{u}} {n : ℕ}
    (P : FunctionalRootChart.{u} L n) :
    FunctionalRootedPattern.{u,0} L n :=
  FunctionalRootExtension.toEnumeratedRootedPattern
    P.root (Equiv.refl (Fin n)) P.ext

/-- An actual finite forbidden piece in an exact full root chart.
This predicate is geometric, not an arbitrary choice of patterns. -/
def FunctionalRootChart.IsForbiddenPiece
    {L : Language.{u}} {n : ℕ}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : FunctionalRootChart.{u} L n) : Prop :=
  P.pattern ∈ forbiddenGeometricFunctionalPieces F n

/-- All selected genuine forbidden pieces of a fixed width, with
their full rooted structure still attached. -/
abbrev SelectedFunctionalChart
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (n : ℕ) :=
  {P : FunctionalRootChart.{u} L n // P.IsForbiddenPiece F}

/-- Two charts are incompatible when their FULL root structures
agree and the corresponding full functional free amalgam belongs
to the forbidden family up to an onto full embedding.

A weak homomorphism is not sufficient here: the free amalgam must
agree on all old relations and complete function value fibres
over the rooted seam. -/
def FunctionalRootChart.Incompatible
    {L : Language.{u}} {n : ℕ}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : FunctionalRootChart.{u} L n) : Prop :=
  ∃ h : P.root = Q.root,
    forbiddenFunctionalGlue P.root F P.ext (h.symm ▸ Q.ext)

/-- The published Myhill--Nerode equivalence, now for ALL genuine
forbidden pieces of fixed width, with arbitrary compatible rooted
charts as tests (not only tests that are themselves forbidden). -/
def globalFunctionalPieceSetoid
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (n : ℕ) : Setoid (SelectedFunctionalChart F n) :=
  pieceSetoid (fun P Q =>
    FunctionalRootChart.Incompatible F P.1 Q)

/-- Global incompatibility-equivalence classes at root width n. -/
abbrev GlobalFunctionalPieceClass
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (n : ℕ) :=
  Quotient (globalFunctionalPieceSetoid F n)

/-- The new relation symbols of the 2019 lift, restricted to
positive widths as in its regularity definition. -/
abbrev GlobalFunctionalPieceSymbol
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop) :=
  Σ k : {n : ℕ // 0 < n}, GlobalFunctionalPieceClass F k.1

/-- Every global new relation symbol has exactly the width of
the class of pieces it indexes. -/
def globalFunctionalPieceArity
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (i : GlobalFunctionalPieceSymbol F) : ℕ :=
  i.1.1

theorem globalFunctionalPieceArity_positive
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (i : GlobalFunctionalPieceSymbol F) :
    0 < globalFunctionalPieceArity F i :=
  i.1.2

/-- The set of ACTUAL root-pattern representatives belonging to
a given global quotient class. No choice of an arbitrary canonical
representative is used to interpret a new relation. -/
def globalFunctionalPieceRepresentatives
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    (i : GlobalFunctionalPieceSymbol F) :
    Set (FunctionalRootedPattern.{u,0} L
      (globalFunctionalPieceArity F i)) :=
  {T | ∃ P : SelectedFunctionalChart F i.1.1,
    Quotient.mk (globalFunctionalPieceSetoid F i.1.1) P = i.2 ∧
    T = P.1.pattern}

/-- The full 2019-style expanded language, using the GLOBAL
quotient classes of actual forbidden pieces in every positive
width; original functions are merely universe-lifted. -/
def globalFunctionalPieceLanguage
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop) :=
  functionalLiftLanguageBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)

/-- Global canonical functional lift, adding one predicate per
actual forbidden piece equivalence class, and no functions.
The extra tuple is present exactly when some genuine piece
from its class has a weak HE realization with distinct roots. -/
def globalFunctionalCanonicalLift
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W) :
    Structure (globalFunctionalPieceLanguage F) W :=
  functionalCanonicalLiftBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F) A

/-- Its old-language shadow equals A exactly, including all
old partial/set-valued function interpretations. -/
@[simp] theorem globalFunctionalCanonicalLift_shadow
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W) :
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (globalFunctionalCanonicalLift F A) = A :=
  functionalShadowBig_canonicalLift L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F) A

/-- The exact semantics of an added global quotient relation,
without accidentally restricting tests or losing root injectivity. -/
theorem globalFunctionalCanonicalRelation_iff
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (i : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F i) → W) :
    (globalFunctionalCanonicalLift F A).rel (.inr i) xs ↔
      Function.Injective xs ∧
      ∃ P : SelectedFunctionalChart F i.1.1,
        Quotient.mk (globalFunctionalPieceSetoid F i.1.1) P = i.2 ∧
        FunctionalRootRealization P.1.pattern A xs := by
  change functionalCanonicalExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (globalFunctionalPieceRepresentatives F) A i xs ↔ _
  constructor
  · rintro ⟨hinj, T, ⟨P, hclass, hT⟩, hreal⟩
    subst T
    exact ⟨hinj, P, hclass, hreal⟩
  · rintro ⟨hinj, P, hclass, hreal⟩
    exact ⟨hinj, P.1.pattern, ⟨P, hclass, rfl⟩, hreal⟩

/-- Every realized global added relation uses an injective root
tuple. This holds independently of the target's additional
possible piece witnesses. -/
theorem globalFunctionalCanonicalRelation_injective
    {L : Language.{u}}
    (F : ∀ {W : Type}, Structure L W → Prop)
    {W : Type} (A : Structure L W)
    (i : GlobalFunctionalPieceSymbol F)
    (xs : Fin (globalFunctionalPieceArity F i) → W)
    (h : (globalFunctionalCanonicalLift F A).rel (.inr i) xs) :
    Function.Injective xs :=
  (globalFunctionalCanonicalRelation_iff F A i xs).mp h |>.1

end AllThoseRamseyClasses.Lifts
