import AllThoseRamseyClasses.Lifts.GeometricGlobalPieceSymbol
import AllThoseRamseyClasses.Lifts.RegularLiftPrecompactness
import Mathlib.Data.Fintype.Card

/-!
# An exact root-width cutoff from a uniform forbidden-source size bound

This is independent of global regularity, image saturation,
maximality, forbidden-image closure, and strong amalgamation.

Every selected chart of width n comes from an ACTUAL finite
forbidden source with a geometric minimal separator enumerated
by an INJECTIVE map Fin n -> source vertices. Thus, if every
forbidden source has at most N vertices, no selected global
piece chart exists at width n>N. The quotient of that empty
selected-chart type is itself empty.

Crucially, this is about the TRUE global 2019 minimal-separator
piece charts, not an auxiliary finite tag language or a fictional
uniform bound on all target source maps. It is one necessary
ingredient of a finite-family regularity bridge, not the bridge
itself: for n<=N the finiteness of quotient classes still needs
a full rooted-isomorphism/representative transport argument.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any actual selected global width-n forbidden piece has
n<=N whenever all finite forbidden source carriers have at most
N vertices. The bound uses the original source size, NOT the
number of vertices in a target image of a weak EHN map. -/
theorem selectedFunctionalChart_width_le_sourceBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    (hBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    {n : ℕ} (P : SelectedFunctionalChart F n) :
    n ≤ N := by
  classical
  have hSelected : IsForbiddenGeometricFunctionalPiece F P.1.pattern := P.2
  obtain ⟨W, A, hFin, hF, d, _hIso⟩ := hSelected
  letI : Finite W := hFin
  letI : Fintype W := Fintype.ofFinite W
  have hCutCard : n ≤ Nat.card W := by
    simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using
      (Fintype.card_le_of_injective d.roots d.roots_injective)
  exact hCutCard.trans (hBound A hF)

/-- Every genuine global piece relation has arity at most the
size cutoff of the source forbidden family. This does not
require regularity, finiteness of the old signature, or positive
old relation/function arities. -/
theorem globalFunctionalPieceSymbol_arity_le_sourceBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N : ℕ)
    (hBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    (s : GlobalFunctionalPieceSymbol F) :
    globalFunctionalPieceArity F s ≤ N := by
  classical
  rcases s with ⟨⟨n, hn⟩, q⟩
  change n ≤ N
  exact selectedFunctionalChart_width_le_sourceBound
    F N hBound (Quotient.out q)

/-- Above the original forbidden-source size cutoff there are
NO true selected global piece equivalence classes: the actual
quotient carrier is empty, not merely a finite set of unknown
classes. -/
theorem globalFunctionalPieceClass_isEmpty_above_sourceBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N n : ℕ)
    (hBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    (hTooLarge : N < n) :
    IsEmpty (GlobalFunctionalPieceClass F n) := by
  classical
  refine ⟨fun q => ?_⟩
  have hWidth : n ≤ N :=
    selectedFunctionalChart_width_le_sourceBound
      F N hBound (Quotient.out q)
  exact (not_le_of_gt hTooLarge) hWidth

/-- Finiteness at all root widths above the bound is immediate
from emptiness; the only remaining regularity work is for the
finitely many widths 1,...,N, and only for their REAL quotient
classes. -/
theorem globalFunctionalPieceClass_finite_above_sourceBound
    (F : ∀ {W : Type}, Structure L W → Prop)
    (N n : ℕ)
    (hBound : ∀ {W : Type} (A : Structure L W),
      F A → Nat.card W ≤ N)
    (hTooLarge : N < n) :
    Finite (GlobalFunctionalPieceClass F n) := by
  letI : IsEmpty (GlobalFunctionalPieceClass F n) :=
    globalFunctionalPieceClass_isEmpty_above_sourceBound
      F N n hBound hTooLarge
  infer_instance

end AllThoseRamseyClasses.Lifts
