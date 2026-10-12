import AllThoseRamseyClasses.Published.MinimalNoncommonHJ2019
import PartiteConstruction.Ramsey.ClosurePictureCoordinate

/-!
# Exceptional constant Hales--Jewett coordinates factor through an actual A-copy

The remaining transverse higher-rank 2019 Picture step needs two
different ordinary side maps to the old U-closed picture with a common
root factorization through two embedded copies of the SAME A∈K.

A minimal no-common-coordinate selected native line family T
has, for each exceptional i∈T, a coordinate k_rest which is
VARIABLE on every other line but CONSTANT on line i.

The constant letter at that coordinate is not merely a label: it
is a genuine part-preserving INDUCED embedding of the selected A
into the original Old.restrict alpha system. Composing with the
actual inclusion of the support into Old yields a full embedding
a : A -> Old.

For EVERY support vertex x on the exceptional attached old-copy
line, evaluating its native line image at k_rest is exactly
a(R.part x). Thus the old-picture root image on that side factors
through a SINGLE selected embedded A-copy, with q = old part.

The second theorem applies this to an arbitrary source root whose
core image lies on the actual exceptional line, without assuming
the root is intrinsically closed or irreducible.

The final theorem selects such a constant-letter A embedding for
every exceptional line of a minimal transverse family.

Still open: the OTHER side map of an arbitrary maximal-rank
source free cut must have a compatible A-root factorization.
The two side projections are not forced to agree as old vertices,
and their common part labels alone do not supply this second
A-embedding. This module does not prove rank promotion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}} {P Q V I H : Type v} {N : ℕ}

/-- If an actual Hales--Jewett line has a CONSTANT letter at
coordinate k, evaluating its old-support line map at k factors
through one fixed full induced A-copy a : A ↪ Old.

The factorization is on ALL vertices of the real selected support,
not merely on a supplied small root. -/
theorem native2019_constant_line_evaluation_factors_A
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i : I) (k : Fin N)
    (hConstant : (lines i).symbol k ≠ .parameter) :
    ∃ a : Embedding A Old.toRelStructure,
      (∀ x : Old.support alpha,
        ((NonInduced.lineMap (lines i) x).coord k).1 =
          a ((Old.restrict alpha).part x)) ∧
      (∀ q : Q, Old.part (a q) = alpha q) := by
  cases hSymbol : (lines i).symbol k with
  | parameter =>
      exact False.elim (hConstant hSymbol)
  | const letter =>
      let inc : Embedding (Old.restrict alpha).toRelStructure
          Old.toRelStructure :=
        inclusion Old.toRelStructure (Old.support alpha)
      let a : Embedding A Old.toRelStructure :=
        inc.comp letter.toEmbedding
      refine ⟨a, ?_, ?_⟩
      · intro x
        change ((NonInduced.lineMap (lines i) x).coord k).1 =
          (letter ((Old.restrict alpha).part x)).1
        simp [NonInduced.lineMap, hSymbol]
      · intro q
        change Old.part (letter q).1 = alpha q
        calc
          Old.part (letter q).1 =
              alpha ((Old.restrict alpha).part (letter q)) :=
                (Old.restrictedPart_spec alpha (letter q)).symm
          _ = alpha q :=
              congrArg alpha (letter.map_part q)

/-- A source root with its actual core vertices ON ONE
exceptional Hales--Jewett line has a complete fixed A-copy
factorization under the constant-coordinate old evaluation.

Its source carrier H need not be finite, U-closed or irreducible;
the existence of a common embedded A-copy is a property of
the genuine line geometry, not of a hypothetical K-completion. -/
theorem native2019_exceptional_line_root_factors_A
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (i : I) (k : Fin N)
    (hConstant : (lines i).symbol k ≠ .parameter)
    (g : H → NonInduced.Vertex (Old.restrict alpha) N)
    (hOnLine : ∀ r : H,
      ∃ x : Old.support alpha,
        g r = NonInduced.lineMap (lines i) x) :
    ∃ a : Embedding A Old.toRelStructure,
      (∀ q : Q, Old.part (a q) = alpha q) ∧
      (∀ r : H,
        ((g r).coord k).1 = a ((g r).part)) := by
  obtain ⟨a, hFactor, hPart⟩ :=
    native2019_constant_line_evaluation_factors_A
      Old alpha A lines i k hConstant
  refine ⟨a, hPart, ?_⟩
  intro r
  obtain ⟨x, hx⟩ := hOnLine r
  rw [hx]
  exact hFactor x

/-- The minimal transverse Hales--Jewett obstruction has an
ACTUAL embedded A-letter boundary on its exceptional line
when evaluated at the rest-side common variable coordinate.

This is one of the TWO A-root factorizations needed for the
maximal weak-side gluing theorem; the other is still open. -/
theorem native2019_minimal_transverse_exceptional_letter_boundaries
    [DecidableEq I]
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (S : Finset I)
    (hNoCommon : ¬ ∃ k : Fin N,
      ∀ i ∈ S, (lines i).symbol k = .parameter) :
    ∃ T : Finset I, T ⊆ S ∧
      (¬ ∃ k : Fin N,
        ∀ i ∈ T, (lines i).symbol k = .parameter) ∧
      (∀ i ∈ T, ∃ k : Fin N,
        (lines i).symbol k ≠ .parameter ∧
        (∀ j ∈ T.erase i,
          (lines j).symbol k = .parameter) ∧
        ∃ a : Embedding A Old.toRelStructure,
          (∀ x : Old.support alpha,
            ((NonInduced.lineMap (lines i) x).coord k).1 =
              a ((Old.restrict alpha).part x)) ∧
          (∀ q : Q, Old.part (a q) = alpha q)) := by
  obtain ⟨T, hTS, hTBad, hMinimal⟩ :=
    exists_minimal_noncommon_HJ_lines lines S hNoCommon
  refine ⟨T, hTS, hTBad, ?_⟩
  intro i hi
  obtain ⟨k, hConst, hOthers⟩ := hMinimal i hi
  obtain ⟨a, hFac, hPart⟩ :=
    native2019_constant_line_evaluation_factors_A
      Old alpha A lines i k hConst
  exact ⟨k, hConst, hOthers, a, hFac, hPart⟩

end AllThoseRamseyClasses.Published
