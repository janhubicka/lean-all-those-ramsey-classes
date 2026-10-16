import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift

/-!
# Global piece equivalence restricts to the fixed FULL root profile

The global Section 3 piece-equivalence relation compares forbidden
pieces by their sets of incompatible tests over ALL rooted charts,
which may have different induced root structures.

If two selected pieces have the SAME full functional root structure
Root (on the ordered carrier Fin n), their global equivalence is
EXACTLY the already verified fixed-root incompatibility equivalence
of `functionalRootPieceSetoid Root F`.

This is not merely an arbitrary identification of languages: the
global incompatibility predicate explicitly requires equality of
the entire root structure before two pieces may be freely glued,
including all function domains and values. Tests with another root
are incompatible with neither piece; tests with Root are precisely
the old fixed-root tests.

A separate theorem is needed to prove that two eligible forbidden
pieces with DIFFERENT full roots cannot have equal profiles. That
requires a genuine forbidden complement test (nonempty
incompatibility profile), which is supplied geometrically by a
finite connected forbidden witness rather than by proof irrelevance.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- A full functional root extension as a chart of its own width. -/
def FunctionalRootChart.ofExtension
    (Root : Structure L (Fin n))
    (P : FunctionalRootExtension Root) :
    FunctionalRootChart.{u} L n where
  root := Root
  ext := P

/-- When the two charts have the SAME full root, their global
incompatibility test is exactly canonical functional free gluing.
No root-isomorphism coercion, extra temporary function, or
partial function fibre approximation is introduced. -/
theorem chartIncompatible_sameRoot_iff
    (Root : Structure L (Fin n))
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : FunctionalRootExtension Root) :
    FunctionalRootChart.Incompatible F
      (FunctionalRootChart.ofExtension Root P)
      (FunctionalRootChart.ofExtension Root Q) ↔
        forbiddenFunctionalGlue Root F P Q := by
  constructor
  · rintro ⟨h, hbad⟩
    have heq : h = rfl := Subsingleton.elim _ _
    rw [heq] at hbad
    change forbiddenFunctionalGlue Root F P Q at hbad
    exact hbad
  · intro hbad
    exact ⟨rfl, hbad⟩

/-- Global Myhill--Nerode equivalence is the same as fixed-root
canonical equivalence for selected forbidden pieces with a
specified identical full functional root. This is the chart-wise
bridge for the GLOBAL new relation symbols of the 2019 lift. -/
theorem globalFunctionalPiece_equiv_iff_fixedRoot
    (Root : Structure L (Fin n))
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : FunctionalRootExtension Root)
    (hP : (FunctionalRootChart.ofExtension Root P).IsForbiddenPiece F)
    (hQ : (FunctionalRootChart.ofExtension Root Q).IsForbiddenPiece F) :
    (globalFunctionalPieceSetoid F n).r
      ⟨FunctionalRootChart.ofExtension Root P, hP⟩
      ⟨FunctionalRootChart.ofExtension Root Q, hQ⟩ ↔
    (functionalRootPieceSetoid Root F).r P Q := by
  constructor
  · intro hglobal
    apply (functionalRootPiece_equiv_iff Root F P Q).mpr
    intro Test
    let T : FunctionalRootChart.{u} L n :=
      FunctionalRootChart.ofExtension Root Test
    have htest :
        FunctionalRootChart.Incompatible F
          (FunctionalRootChart.ofExtension Root P) T ↔
        FunctionalRootChart.Incompatible F
          (FunctionalRootChart.ofExtension Root Q) T :=
      incompatible_iff_of_equiv hglobal T
    exact ((chartIncompatible_sameRoot_iff Root F P Test).symm.trans
      htest).trans (chartIncompatible_sameRoot_iff Root F Q Test)
  · intro hfixed
    apply equiv_of_incompatible_iff
    intro T
    have htest : ∀ U : FunctionalRootExtension Root,
      forbiddenFunctionalGlue Root F P U ↔
      forbiddenFunctionalGlue Root F Q U :=
      (functionalRootPiece_equiv_iff Root F P Q).mp hfixed
    constructor
    · rintro ⟨hr, hpT⟩
      change Root = T.root at hr
      exact ⟨hr, (htest (hr.symm ▸ T.ext)).mp hpT⟩
    · rintro ⟨hr, hqT⟩
      change Root = T.root at hr
      exact ⟨hr, (htest (hr.symm ▸ T.ext)).mpr hqT⟩

/-- The globally selected piece's own full root is a concrete
functional root structure. This provides a fixed chart for
interpreting its chosen equivalence-class relation. -/
theorem selectedChart_hasFullRoot
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n) :
    ∃ Root : Structure L (Fin n),
      ∃ E : FunctionalRootExtension Root,
        P.1 = FunctionalRootChart.ofExtension Root E :=
  ⟨P.1.root, P.1.ext, rfl⟩


/-- If a selected forbidden piece has at least ONE forbidden rooted
complement, equality of global incompatibility profiles forces
equality of the COMPLETE induced functional root structures.
This is the precise nonempty-profile step needed before
identifying global classes with fixed-root classes. -/
theorem globalFunctionalPiece_equiv_forces_root_eq
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : SelectedFunctionalChart F n)
    (hEq : (globalFunctionalPieceSetoid F n).r P Q)
    (hNonempty : ∃ T : FunctionalRootChart.{u} L n,
      FunctionalRootChart.Incompatible F P.1 T) :
    P.1.root = Q.1.root := by
  obtain ⟨T, hPT⟩ := hNonempty
  have hQT : FunctionalRootChart.Incompatible F Q.1 T :=
    (incompatible_iff_of_equiv hEq T).mp hPT
  obtain ⟨hP, _⟩ := hPT
  obtain ⟨hQ, _⟩ := hQT
  exact hP.trans hQ.symm

end AllThoseRamseyClasses.Lifts
