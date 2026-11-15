import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep

/-!
# Exact A-active SOURCE partition of a full native selected-Q replacement

A genuine full source free amalgam Q +_R E covers every NEW source
vertex by an inserted-Q vertex or a retained-complement E vertex.
Those two images overlap exactly on the full ROOT R.

For ANY target set Active and ANY weak map on the new source,
its actual Active-SOURCE vertex set is the DISJOINT union of:
* Active source vertices inherited through the complete E embedding;
* Active SOURCE vertices inserted from Q but lying outside the Q root.

The disjointness is a FULL native overlap fact; it does not mean
the weak map is injective or that distinct images are counted.
It is the exact source partition needed for quantitative
A-support change, independently of any one-sidedness assumption.

This does not prove that a canonical Q exists with no new
A-active nonroot vertices, nor complete original 2019 Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every A-active actual NEW SOURCE vertex of a full native
Q +_R E amalgam belongs either to the retained E-image or
to the inserted Q-NONROOT image, and the two cases exhaust
the complete source A-support.

Root vertices in the Q-image are redirected to the E-side
using EXACT source overlap; no quotient by target images. -/
theorem fullNativeSelectedQ_Aactive_support_partition
    {W Q E R UT : Type}
    {New : Structure L W}
    {Replacement : Structure L Q}
    {Complement : Structure L E}
    {Root : Structure L R}
    (sQ : Structure.Embedding Root Replacement)
    (sE : Structure.Embedding Root Complement)
    (iQ : Structure.Embedding Replacement New)
    (iE : Structure.Embedding Complement New)
    (hFree : Structure.IsFreeAmalgam sQ sE iQ iE)
    (flip : W → UT) (Active : Set UT) :
    {w : W | flip w ∈ Active} =
      (iE '' {e : E | flip (iE e) ∈ Active}) ∪
      (iQ '' {q : Q | q ∉ Set.range sQ ∧
        flip (iQ q) ∈ Active}) := by
  classical
  ext w
  constructor
  · intro hw
    change flip w ∈ Active at hw
    rcases hFree.covers w with ⟨q, hqw⟩ | ⟨e, hew⟩
    · by_cases hRoot : q ∈ Set.range sQ
      · obtain ⟨r, hr⟩ := hRoot
        have hOverlap : iQ (sQ r) = iE (sE r) :=
          (hFree.overlap (sQ r) (sE r)).mpr
            ⟨r, rfl, rfl⟩
        have hEw : iE (sE r) = w := by
          calc
            iE (sE r) = iQ (sQ r) := hOverlap.symm
            _ = iQ q := congrArg iQ hr
            _ = w := hqw.symm
        have hEActive : flip (iE (sE r)) ∈ Active := by
          rw [hEw]
          exact hw
        exact Or.inl ⟨sE r, hEActive, hEw⟩
      · have hQA : flip (iQ q) ∈ Active := by
          simpa only [← hqw] using hw
        exact Or.inr ⟨q, ⟨hRoot, hQA⟩, hqw.symm⟩
    · have heA : flip (iE e) ∈ Active := by
        rw [← hew]
        exact hw
      exact Or.inl ⟨e, heA, hew.symm⟩
  · intro hw
    rcases hw with ⟨e, heA, rfl⟩ | ⟨q, hqA, rfl⟩
    · exact heA
    · exact hqA.2

/-- The two full-native source pieces in the A-support
decomposition above are disjoint. If their SOURCE images
met, the Q source vertex would necessarily be on Q's
shared root, contradicting the Q-nonroot membership. -/
theorem fullNativeSelectedQ_Aactive_partition_disjoint
    {W Q E R UT : Type}
    {New : Structure L W}
    {Replacement : Structure L Q}
    {Complement : Structure L E}
    {Root : Structure L R}
    (sQ : Structure.Embedding Root Replacement)
    (sE : Structure.Embedding Root Complement)
    (iQ : Structure.Embedding Replacement New)
    (iE : Structure.Embedding Complement New)
    (hFree : Structure.IsFreeAmalgam sQ sE iQ iE)
    (flip : W → UT) (Active : Set UT) :
    Disjoint
      (iE '' {e : E | flip (iE e) ∈ Active})
      (iQ '' {q : Q | q ∉ Set.range sQ ∧
        flip (iQ q) ∈ Active}) := by
  apply Set.disjoint_left.mpr
  intro w hwE hwQ
  obtain ⟨e, _heA, hew⟩ := hwE
  obtain ⟨q, hqA, hqw⟩ := hwQ
  have hOver : iQ q = iE e := hqw.trans hew.symm
  obtain ⟨r, hrQ, _hrE⟩ := (hFree.overlap q e).mp hOver
  exact hqA.1 ⟨r, hrQ.symm⟩

/-- Specialize the exact disjoint decomposition to the REAL
selected-Q original geometric flip, using the original
weak-map target coordinates on the ENTIRE retained complement.

The E-side A-support is measured using OLD source target values;
the Q-private side is measured using NEW source target values.
This holds even when the removed old component is not A-free. -/
theorem geometricSelectedQ_Aactive_support_disjoint_oldE_newQ
    {V W UT : Type}
    (Old : Structure L V)
    {m : ℕ}
    (inner : GeometricFunctionalPieceData Old m)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old inner).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old inner).str New)
    (hNewFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE)
    (f : V → UT) (flip : W → UT)
    (Active : Set UT)
    (hEAgree : ∀ e : (geometricGlobalComplementChart Old inner).Carrier,
      flip (iE e) = f e.1) :
    {w : W | flip w ∈ Active} =
      (iE '' {e : (geometricGlobalComplementChart Old inner).Carrier |
        f e.1 ∈ Active}) ∪
      (iQ '' {q : Q.Carrier | q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ Active}) ∧
    Disjoint
      (iE '' {e : (geometricGlobalComplementChart Old inner).Carrier |
        f e.1 ∈ Active})
      (iQ '' {q : Q.Carrier | q ∉ Set.range Q.rootEmbedding ∧
        flip (iQ q) ∈ Active}) := by
  have hESupport :
      {e : (geometricGlobalComplementChart Old inner).Carrier |
        flip (iE e) ∈ Active} =
      {e : (geometricGlobalComplementChart Old inner).Carrier |
        f e.1 ∈ Active} := by
    ext e
    change (flip (iE e) ∈ Active) ↔ (f e.1 ∈ Active)
    rw [hEAgree e]
  have hPartition :=
    fullNativeSelectedQ_Aactive_support_partition
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE hNewFree flip Active
  have hDisjoint :=
    fullNativeSelectedQ_Aactive_partition_disjoint
      Q.rootEmbedding
      (geometricGlobalComplementChart Old inner).rootEmbedding
      iQ iE hNewFree flip Active
  rw [hESupport] at hPartition hDisjoint
  exact ⟨hPartition, hDisjoint⟩

end AllThoseRamseyClasses.Lifts
