import AllThoseRamseyClasses.Published.FunctionalWithParts2019AmbientHullRootGlue
import AllThoseRamseyClasses.Published.FunctionalWithParts2019RankOneRootGlue
import PartiteConstruction.Ramsey.ClosureFreeAmalgamClosedRoot
import PartiteConstruction.Relational.FreeAmalgamationClass

/-!
# Track C: actual weak VERTEX cutoff, no closed generating-rank premise

The corrected 2019 class-local axiom tests every exact ambient-induced
weak OLD source S with at most n VERTICES. This is different from the
stronger closed U-generator-rank-n premise used in earlier conditional
rank-step theorems.

This module isolates a direct consequence of the actual weak vertex
cutoff. Every full embedded small weak SOURCE has an H-relative
completion: take its exact finite range in C, apply the supplied
small-test premise, and pull the protected completion map back along
the full embedding. No source hull or extra vertices are introduced.

If an arbitrary weak source has a true full free cut with both side
ranges relatively U-closed, each side has at most n vertices, and its
common Root is a canonical K(H) object, then the verified H-valued
gluing theorem completes the WHOLE weak source. In particular any
noncompletable weak source admits no such canonical-root cut.

This does NOT assert that an arbitrary bad weak source has a cut, or
that corrected (4b) makes a reducible root canonical. No original
intrinsic-to-ambient functional local-axiom implication is proved.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V X Y RootV LeftV RightV WholeV : Type w}

/-- Exact H-relative completability pulls back along any FULL
relational embedding, retaining the original OLD mask predicates.
There is no U-closedness requirement on the weak source. -/
theorem genuineTagged2019_relativeCompletion_precomp_embedding
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    {A : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) X}
    {B : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Y}
    (e : Embedding A B)
    (hB : HasGenuinePartiteTagged2019RelativeCompletion H B) :
    HasGenuinePartiteTagged2019RelativeCompletion H A := by
  classical
  obtain ⟨Z, hZ, Target, targetPart, hH, hTr, hIrred, f, hf⟩ := hB
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hPull : IsInducedClosedUHomomorphismEmbedding
      rules A
      (wholeMaskTagExpansion (withPartsWholeMaskOld Target targetPart))
      (f ∘ e.toFun) :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (IsClosedUHomomorphismEmbedding.precomp_embedding
        (IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hf)
        e)
  exact ⟨Z, hZ, Target, targetPart, hH, hTr, hIrred, f ∘ e.toFun, hPull⟩

/-- Actual n-VERTEX weak completability in C also completes any
possibly nonclosed weak D of at most n original vertices that FULLY
embeds into C. The exact source D is never replaced by its hull. -/
theorem genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (n : ℕ)
    (hSmall : ∀ (S : Finset V), S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set V)))
    (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) X)
    [Finite X]
    (e : Embedding D C)
    (hCard : Nat.card X ≤ n) :
    HasGenuinePartiteTagged2019RelativeCompletion H D := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let S : Finset V := Finset.univ.image e.toFun
  have hSize : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset X).card := Finset.card_image_le
      _ = Fintype.card X := Finset.card_univ
      _ = Nat.card X := by rw [Nat.card_eq_fintype_card]
      _ ≤ n := hCard
  let intoRange : Embedding D (C.induce (↑S : Set V)) := {
    toFun := fun x => ⟨e x, by
      change e x ∈ S
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_univ x, rfl⟩⟩
    injective := by
      intro x y hxy
      apply e.injective
      exact congrArg Subtype.val hxy
    map_rel_iff := by
      intro R xs
      change C.rel R (e.toFun ∘ xs) ↔ D.rel R xs
      exact e.map_rel_iff R xs
  }
  exact genuineTagged2019_relativeCompletion_precomp_embedding
    H intoRange (hSmall S hSize)

/-- The exact weak n-vertex premise suffices for gluing if a
particular full free cut is already provided with a canonical
common H-root. The higher U-generator-rank invariant is not
used: both side completions come from original n-vertex tests. -/
theorem genuineTagged2019_weakVertexCutoff_glue_canonicalRoot
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.rightIn))
    (hLeftSmall : Nat.card d.Left ≤ n)
    (hRightSmall : Nat.card d.Right ≤ n)
    (hRootK : canonicalGenuineTagged2019Class H d.common) :
    HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)) := by
  classical
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  let intoC : Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  let eLeft : Embedding d.left C := intoC.comp d.leftIn
  let eRight : Embedding d.right C := intoC.comp d.rightIn
  have hLeft : HasGenuinePartiteTagged2019RelativeCompletion H d.left :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall d.left eLeft hLeftSmall
  have hRight : HasGenuinePartiteTagged2019RelativeCompletion H d.right :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall d.right eRight hRightSmall
  exact genuinePartite2019_relativeCompletion_glue_over_H_root
    H hStrong hKIrr d.free hL hR hRootK hLeft hRight

/-- Genuine counterdirection: if all exact ambient weak tests of
at most n vertices are completable but Whole is not, EVERY free
cut with relatively closed sides of size at most n necessarily has
a NONCANONICAL common root. No closed U-rank assumption is used. -/
theorem genuineTagged2019_badWeak_vertexCutoff_no_canonicalRootCut
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.rightIn))
    (hLeftSmall : Nat.card d.Left ≤ n)
    (hRightSmall : Nat.card d.Right ≤ n) :
    ¬ canonicalGenuineTagged2019Class H d.common := by
  intro hRootK
  exact hBad (genuineTagged2019_weakVertexCutoff_glue_canonicalRoot
    H hStrong hKIrr C n hSmall S d
    hL hR hLeftSmall hRightSmall hRootK)


/-- Under actual H-isomorphism invariance and corrected (4b), an
eligible relatively U-closed proper cut of a noncompletable exact
weak test cannot have a common Root which is simultaneously
intrinsically U-closed and U-irreducible.

This is a vertex-cutoff strengthening of the canonical-root
obstruction: it uses only the small induced weak n-vertex completion
premise, NOT a generator-rank-n invariant. -/
theorem genuineTagged2019_badWeak_vertexCutoff_root_closure_or_irred_failure
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.rightIn))
    (hLeftSmall : Nat.card d.Left ≤ n)
    (hRightSmall : Nat.card d.Right ≤ n) :
    (¬ IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) d.common) ∨
    (¬ IsUIrreducible
        ((L.withParts Parts).wholeMaskClosureRules Parts) d.common) := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hNotK : ¬ canonicalGenuineTagged2019Class H d.common :=
    genuineTagged2019_badWeak_vertexCutoff_no_canonicalRootCut
      H hStrong hKIrr C n hSmall S hBad d
      hL hR hLeftSmall hRightSmall
  let K : ∀ {Z : Type w},
      RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z → Prop :=
    canonicalGenuineTagged2019Class H
  have hKIso : IsomorphismClosed2019 K :=
    canonicalGenuineTagged2019Class_isomorphismClosed H hIso
  have hAbstract : ClosedUIrreduciblesIn K rules C :=
    correctedInducedCoverage_toAbstract_2019 hKIso hCovered
  let inc : Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  let eRoot : Embedding d.common C :=
    inc.comp (d.leftIn.comp d.toLeft)
  have hNotBoth :
      ¬ (IsUClosed rules d.common ∧
        IsUIrreducible rules d.common) := by
    rintro ⟨hRootClosed, hRootIrred⟩
    exact hNotK (hAbstract d.common hRootClosed hRootIrred eRoot)
  exact not_and_or.mp hNotBoth


/-- Original n-vertex weak-test completions suffice to glue even a
NONCLOSED weak Root when that root is ordinary irreducible, provided
BOTH auxiliary AMBIENT side closure hulls themselves have at most n
vertices. No bound on their minimum generating rank is used.

The root hull becomes a canonical K(H) support by corrected (4b).
All auxiliary hulls are used only to select H-target completions;
the final completion is on the exact original weak Whole. -/
theorem genuineTagged2019_weakVertexCutoff_glue_irredRoot_of_smallHulls
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    {Root : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RootV}
    {Left : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) LeftV}
    {Right : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RightV}
    {Whole : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole C)
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iL))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      Whole (Set.range iR))
    (hRootIrred : Root.Irreducible)
    (hLeftHullSmall :
      Nat.card (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range (eWhole.comp iL).toFun)) ≤ n)
    (hRightHullSmall :
      Nat.card (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range (eWhole.comp iR).toFun)) ≤ n) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let LeftHull : Set V := UClosureHull rules C
    (Set.range (eWhole.comp iL).toFun)
  let RightHull : Set V := UClosureHull rules C
    (Set.range (eWhole.comp iR).toFun)
  have hLeftComplete :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce LeftHull) :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall (C.induce LeftHull)
      (inclusion C LeftHull) hLeftHullSmall
  have hRightComplete :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce RightHull) :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall (C.induce RightHull)
      (inclusion C RightHull) hRightHullSmall
  exact genuinePartite2019_relativeCompletion_glue_irreducibleRoot_hull
    H hStrong hKIrr C hCClosed hCovered
    hFree eWhole hL hR hRootIrred
    hLeftComplete hRightComplete

/-- Quantitative necessary obstruction AT THE PRINTED VERTEX CUTOFF:
if an exact ambient weak S is not H-completable but admits a
proper relatively U-closed free split over an ordinary irreducible
root, then at least one ambient SIDE CLOSURE HULL contains MORE
than n vertices, although the weak sides themselves may be small.

This is precisely why a closed generator-rank bound on the side
hulls is not a consequence of the printed n-vertex premise.
It is a necessary obstruction, not an assertion that such bad S
exists or that the actual Picture history must incur the overrun. -/
theorem genuineTagged2019_badWeak_irredRoot_forces_hullCard_overrun
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hL : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.leftIn))
    (hR : IsUSubstructure
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)) (Set.range d.rightIn))
    (hRootIrred : d.common.Irreducible) :
    n < Nat.card (UClosureHull
      ((L.withParts Parts).wholeMaskClosureRules Parts) C
      (Set.range ((inclusion C (↑S : Set V)).comp d.leftIn).toFun)) ∨
    n < Nat.card (UClosureHull
      ((L.withParts Parts).wholeMaskClosureRules Parts) C
      (Set.range ((inclusion C (↑S : Set V)).comp d.rightIn).toFun)) := by
  classical
  by_contra hNoOverrun
  have hNoBoth := not_or.mp hNoOverrun
  have hLeftHullSmall :
      Nat.card (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range ((inclusion C (↑S : Set V)).comp d.leftIn).toFun)) ≤ n :=
    Nat.le_of_not_gt hNoBoth.1
  have hRightHullSmall :
      Nat.card (UClosureHull
        ((L.withParts Parts).wholeMaskClosureRules Parts) C
        (Set.range ((inclusion C (↑S : Set V)).comp d.rightIn).toFun)) ≤ n :=
    Nat.le_of_not_gt hNoBoth.2
  let eWhole : Embedding (C.induce (↑S : Set V)) C :=
    inclusion C (↑S : Set V)
  have hWholeComplete :
      HasGenuinePartiteTagged2019RelativeCompletion
        H (C.induce (↑S : Set V)) :=
    genuineTagged2019_weakVertexCutoff_glue_irredRoot_of_smallHulls
      H hStrong hKIrr C hCClosed hCovered n hSmall
      d.free eWhole hL hR hRootIrred
      hLeftHullSmall hRightHullSmall
  exact hBad hWholeComplete



/-- At the actual n-VERTEX weak test cutoff, an U-CLOSED
whole that is the full free amalgam of U-CLOSED sides of at
most n vertices is H-relatively completable whenever its
automatically U-CLOSED common root has USize ≤ 1.

Root closure follows from the exact closed free-amalgam root
lemma. The sides are completed by exact n-vertex weak tests
in the same ambient C. There is NO closed generator-rank-j
invariant or separately chosen compatible H-boundary. -/
theorem genuineTagged2019_weakVertexCutoff_glue_closed_rankOneRoot
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    {Root : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RootV}
    {Left : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) LeftV}
    {Right : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RightV}
    {Whole : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole C)
    (hWholeClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Whole)
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Left)
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Right)
    [Fintype RootV]
    [Finite LeftV] [Finite RightV]
    (hRootRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root ≤ 1)
    (hLeftSmall : Nat.card LeftV ≤ n)
    (hRightSmall : Nat.card RightV ≤ n) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hRootClosed : IsUClosed rules Root :=
    hFree.root_isUClosed_of_closed_whole_and_sides
      hWholeClosed hLeftClosed hRightClosed
  have hRelLeft : IsUSubstructure rules Whole (Set.range iL) :=
    iL.range_isUSubstructure hLeftClosed hWholeClosed
  have hRelRight : IsUSubstructure rules Whole (Set.range iR) :=
    iR.range_isUSubstructure hRightClosed hWholeClosed
  have hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall Left (eWhole.comp iL) hLeftSmall
  have hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall Right (eWhole.comp iR) hRightSmall
  exact genuinePartite2019_relativeCompletion_glue_over_rankOne_root
    H hStrong hIso hKIrr C hCovered
    hFree eWhole hRelLeft hRelRight hRootClosed hRootRank
    hLeft hRight

/-- A genuine BAD weak source satisfying the exact small
n-vertex test premise cannot be a CLOSED free amalgam of
CLOSED sides of ≤n vertices over a U-rank-one root. In fact,
EVERY such free cut has common-root USize at least two.
The premise is on n vertices, not n generators. -/
theorem genuineTagged2019_badWeak_closedCut_rootRank_ge_two
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hWholeClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)))
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) d.left)
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) d.right)
    (hLeftSmall : Nat.card d.Left ≤ n)
    (hRightSmall : Nat.card d.Right ≤ n)
    [Fintype d.Common] :
    1 < USize ((L.withParts Parts).wholeMaskClosureRules Parts)
      d.common := by
  classical
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  -- Keep the caller's Fintype d.Common: introducing a second local
  -- instance makes the two USize expressions use different enumerations.
  by_contra hNoRankTwo
  have hRank : USize
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      d.common ≤ 1 := by omega
  have hWhole : HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)) :=
    genuineTagged2019_weakVertexCutoff_glue_closed_rankOneRoot
      H hStrong hIso hKIrr C hCovered n hSmall
      d.free (inclusion C (↑S : Set V))
      hWholeClosed hLeftClosed hRightClosed
      hRank hLeftSmall hRightSmall
  exact hBad hWhole


/-- At the printed n-VERTEX weak cutoff, a U-CLOSED Whole which is
a free amalgam of U-CLOSED sides of ≤n vertices over an
U-IRREDUCIBLE Root has an H-relative completion. Root
closedness is automatic by the verified closed-root
intersection theorem. Corrected (4b) makes that SAME
root a canonical H-member, without a generating-rank
assumption or enlargement of the weak source. -/
theorem genuineTagged2019_weakVertexCutoff_glue_closed_UIrredRoot
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    {Root : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RootV}
    {Left : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) LeftV}
    {Right : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) RightV}
    {Whole : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) WholeV}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (eWhole : Embedding Whole C)
    (hWholeClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Whole)
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Left)
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) Right)
    [Finite LeftV] [Finite RightV]
    (hRootUIrred : IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts) Root)
    (hLeftSmall : Nat.card LeftV ≤ n)
    (hRightSmall : Nat.card RightV ≤ n) :
    HasGenuinePartiteTagged2019RelativeCompletion H Whole := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  have hRootClosed : IsUClosed rules Root :=
    hFree.root_isUClosed_of_closed_whole_and_sides
      hWholeClosed hLeftClosed hRightClosed
  have hRelLeft : IsUSubstructure rules Whole (Set.range iL) :=
    iL.range_isUSubstructure hLeftClosed hWholeClosed
  have hRelRight : IsUSubstructure rules Whole (Set.range iR) :=
    iR.range_isUSubstructure hRightClosed hWholeClosed
  have hLeft : HasGenuinePartiteTagged2019RelativeCompletion H Left :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall Left (eWhole.comp iL) hLeftSmall
  have hRight : HasGenuinePartiteTagged2019RelativeCompletion H Right :=
    genuineTagged2019_embeddedWeakSmall_of_vertexCutoff
      H C n hSmall Right (eWhole.comp iR) hRightSmall
  exact genuinePartite2019_relativeCompletion_glue_over_protected_root
    H hStrong hIso hKIrr C hCovered
    hFree eWhole hRelLeft hRelRight
    hRootClosed hRootUIrred hLeft hRight

/-- Every eligible genuinely CLOSED small free cut of a bad weak
test has a U-REDUCIBLE common Root, not merely USize ≥ 2.
This is independent of a closed generator-rank completion
invariant: the only quantitative premise is the original
ambient n-VERTEX weak-test completion hypothesis. -/
theorem genuineTagged2019_badWeak_closedCut_root_notUIrred
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (hStrong : GenuinePartiteStrongAmalgamation2019 H)
    (hIso : GenuinePartiteIsomorphismClosed2019 H)
    (hKIrr : ∀ {Z : Type w}
      (D : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) Z),
      canonicalGenuineTagged2019Class H D → D.Irreducible)
    (C : RelStructure (((L.withParts Parts).wholeMaskTagLanguage Parts)) V)
    [Finite V]
    (hCovered : CorrectedUIrreduciblesIn
      (canonicalGenuineTagged2019Class H)
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (n : ℕ)
    (hSmall : ∀ (T : Finset V), T.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑T : Set V)))
    (S : Finset V)
    (hBad : ¬ HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)))
    (d : ProperFreeDecomposition (C.induce (↑S : Set V)))
    (hWholeClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑S : Set V)))
    (hLeftClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) d.left)
    (hRightClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) d.right)
    (hLeftSmall : Nat.card d.Left ≤ n)
    (hRightSmall : Nat.card d.Right ≤ n) :
    ¬ IsUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      d.common := by
  classical
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  intro hRootUIrred
  have hWhole : HasGenuinePartiteTagged2019RelativeCompletion
      H (C.induce (↑S : Set V)) :=
    genuineTagged2019_weakVertexCutoff_glue_closed_UIrredRoot
      H hStrong hIso hKIrr C hCovered n hSmall
      d.free (inclusion C (↑S : Set V))
      hWholeClosed hLeftClosed hRightClosed
      hRootUIrred hLeftSmall hRightSmall
  exact hBad hWhole

end AllThoseRamseyClasses.Published
