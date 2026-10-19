import AllThoseRamseyClasses.Lifts.GlobalIrreducibleForbiddenStrongAmalgamation
import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift
import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam

/-!
# Irreducible forbidden sources have no genuine global separator pieces

An authentic Section 3 geometric piece must arise from a minimal
function-closed separator between two distinct Gaifman components
of one forbidden source. Such a cut produces a PROPER full native
functional free decomposition of that source.

Hence irreducible forbidden sources have NO genuine geometric pieces,
at ANY root width; therefore the original global incompatibility
quotient has no added relation symbols. This identifies exactly why
the irreducible-source case already has a direct freely ordered
Ramsey theorem, without the additional 2019 homogenizing relations.

This makes no assertion about reducible sources, where genuine
separator pieces and the unresolved global shadow lemma remain.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A genuine minimal closed separator is impossible in a full
functional irreducible source. The component decomposition is a
REAL full functional free amalgam: one side excludes the selected
opposite root, and the other excludes the chosen component root. -/
theorem noGeometricFunctionalPiece_of_irreducible
    {V : Type v}
    (Source : Structure L V)
    (hIrred : Source.Irreducible)
    {n : ℕ} (d : GeometricFunctionalPieceData Source n) :
    False := by
  let R : Set V := Set.range d.roots
  have hR : Source.IsClosed R := d.minimal.1
  have hFree :=
    component_isFreeAmalgam Source R hR d.left
  rcases hIrred hFree (Structure.Embedding.id Source) with hL | hRside
  · obtain ⟨p, hp⟩ := hL d.right.1
    have heq : p.1 = d.right.1 := hp.symm
    rcases p.2 with hpRoot | hpComponent
    · exact d.right.2 (heq ▸ hpRoot)
    · have hLeft : d.right.1 ∈
          functionalComponentFrom Source R d.left := by
        rw [← heq]
        exact hpComponent
      have hRight : d.right.1 ∈
          functionalComponentFrom Source R d.right :=
        functionalComponentFrom_root Source R d.right
      exact (Set.disjoint_left.mp
        (geometricPiece_components_disjoint Source d)) hLeft hRight
  · obtain ⟨q, hq⟩ := hRside d.left.1
    have heq : q.1 = d.left.1 := hq.symm
    have hInside : d.left.1 ∈
        functionalComponentFrom Source R d.left :=
      functionalComponentFrom_root Source R d.left
    exact q.2 (heq ▸ hInside)

/-- Every genuinely selected forbidden-piece chart would supply
an actual minimal separator in a finite forbidden source, violating
the source's native functional irreducibility. -/
theorem noSelectedGlobalChart_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    (n : ℕ) (P : SelectedFunctionalChart F n) :
    False := by
  obtain ⟨W, Source, hFinite, hF, d, _⟩ := P.2
  exact noGeometricFunctionalPiece_of_irreducible
    Source (hIrred Source hFinite hF) d

/-- The ENTIRE new-symbol type of the printed global canonical
forbidden-piece lift is empty if every finite forbidden source
is irreducible. This is stronger than a finite-arity or finite
total-language bound, and needs NO regularity hypothesis. -/
theorem globalPieceSymbols_empty_of_irreducible
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F) :
    IsEmpty (GlobalFunctionalPieceSymbol F) := by
  classical
  refine ⟨?_⟩
  rintro ⟨⟨n, hn⟩, cl⟩
  let P : SelectedFunctionalChart F n := Quotient.out cl
  exact noSelectedGlobalChart_irreducible F hIrred n P

end AllThoseRamseyClasses.Lifts
