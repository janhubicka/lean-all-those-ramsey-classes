import AllThoseRamseyClasses.Published.ExceptionalHJLetterBoundary2019
import PartiteConstruction.Ramsey.ClosureNativeWeakCutBoundary

/-!
# Actual native Hales--Jewett copy/rest overlap factors through one A-letter

A real native Picture attachment over the selected old support S
has an EXACT free split at each attached old-copy index i:
its piece is the selected old copy, its rest omits that copy's
PRIVATE exterior vertices, and their overlap is in the core.

The pinned Attachment.decompose proves the free split. Here we
strengthen its common-root geometry, without assuming source
U-closedness: every overlap vertex is in fact the core image of
a support vertex x under the ACTUAL attaching map of line i.
This distinguishes the overlap from arbitrary core vertices.

When the exceptional Hales--Jewett line is CONSTANT at coordinate k,
that coordinate is an honest A-letter, already a full induced
part-preserving embedding A->Old. The coordinate evaluation of
EVERY overlap vertex is therefore in that ONE fixed A-copy.
We construct a SINGLE root factorization q:Overlap->A, not merely
one letter/part for each vertex independently.

This DISCHARGES the exceptional line's A-boundary factorization
for the literal copy/rest free cut in the actual native attachment.
No arbitrary external completion target is tagged, and no
vertex-exact weak source is enlarged or replaced by a hull.

The OTHER side map must still factor its root coherently through
a second full A embedding into Old, and the source cut must be
proper with the correct rank-j side budgets. These remain open;
the general j-to-j+1 constructor and repaired Theorem 2.18
are NOT claimed here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}
variable {P Q V I : Type v} {N : ℕ}

/-- Every vertex in the ACTUAL overlap of an attached old-copy
piece with its rest has an ORIGINAL selected-support preimage x.
In particular its native core vertex is the line i embedding of x.

No U-closedness or semiclosedness assumption is used. -/
theorem native2019_overlap_has_exceptional_line_preimage
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (T : Set (Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I)))
    (i : I)
    (z : OverlapV Old.toRelStructure (Old.support alpha)
      (power (Old.restrict alpha) N).toRelStructure
      (closureLineMaps Old alpha A hRestricted lines) T i) :
    ∃ x : Old.support alpha,
      z.1.1 = Sum.inl
        ((closureLineMaps Old alpha A hRestricted lines) i x) := by
  let R := Old.restrict alpha
  let Core := (power R N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  obtain ⟨x, hx⟩ := z.2.1
  by_cases hxS : x ∈ Old.support alpha
  · refine ⟨⟨x, hxS⟩, ?_⟩
    exact hx.trans (copyMap_mem i x hxS)
  · have hOut :
        OutsideAt (W := NonInduced.Vertex R N) (I := I)
          (Old.support alpha) i z.1.1 := by
      refine ⟨⟨x, hxS⟩, ?_⟩
      exact hx.trans (copyMap_not_mem i x hxS)
    exact False.elim (z.2.2 hOut)

/-- At a constant coordinate of the exceptional line, the ENTIRE
actual overlap of the source copy/rest cut factors through ONE
full A embedding a : A->Old and ONE root map q : Overlap->A.

The selected root-to-A map q sends a core vertex represented by
lineMap i x to the old selected part of x. The constant letter
embedding fixes A independently of the chosen root vertex. -/
theorem native2019_exceptional_overlap_constant_A_boundary
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (T : Set (Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I)))
    (i : I) (k : Fin N)
    (hConstant : (lines i).symbol k ≠ .parameter) :
    ∃ (a : Embedding A Old.toRelStructure)
      (q : OverlapV Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) T i → Q),
      (∀ r : OverlapV Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) T i,
        Old.part (a (q r)) = alpha (q r)) ∧
      (∀ r : OverlapV Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines) T i,
        ∃ x : Old.support alpha,
          r.1.1 = Sum.inl
            ((closureLineMaps Old alpha A hRestricted lines) i x) ∧
          q r = (Old.restrict alpha).part x ∧
          (((closureLineMaps Old alpha A hRestricted lines) i x).coord k).1 =
            a (q r)) := by
  classical
  let R := Old.restrict alpha
  let maps := closureLineMaps Old alpha A hRestricted lines
  let Root := OverlapV Old.toRelStructure (Old.support alpha)
    (power R N).toRelStructure maps T i
  obtain ⟨a, hFactor, hPart⟩ :=
    native2019_constant_line_evaluation_factors_A
      Old alpha A lines i k hConstant
  have hPreimage (r : Root) :
      ∃ x : Old.support alpha, r.1.1 = Sum.inl (maps i x) :=
    native2019_overlap_has_exceptional_line_preimage
      Old alpha A hRestricted lines T i r
  let x : Root → Old.support alpha :=
    fun r => Classical.choose (hPreimage r)
  let q : Root → Q := fun r => R.part (x r)
  refine ⟨a, q, ?_, ?_⟩
  · intro r
    exact hPart (q r)
  · intro r
    refine ⟨x r, Classical.choose_spec (hPreimage r), rfl, ?_⟩
    change ((NonInduced.lineMap (lines i) (x r)).coord k).1 =
      a (R.part (x r))
    exact hFactor (x r)

end AllThoseRamseyClasses.Published
