import AllThoseRamseyClasses.Published.InducedClosed2019MaximalWeakTwoSide

/-!
# Genuine weak K-completion from TWO old side maps with a CLOSED K-root

The corrected 2019 higher-rank native proof must glue old-picture
completions of the two sides of an actual source free amalgam over
ONE valid CLOSED K-boundary. Equality of part labels or arbitrary
noninjective protected root maps to the selected A are not enough.

There is a useful non-A-letter special case: if the literal
source separator Root is ITSELF a finite U-closed member of K,
then no additional arbitrary A-copy is needed. Every K-member
is ordinarily irreducible by the class hypothesis. Restrict each
ORDINARY old-side homomorphism-embedding to that irreducible
source root. It becomes a FULL induced embedding of Root into
the old Picture. Both embeddings are compatible with ONE root
map q=id_Root, by construction.

The already CI-verified maximal weak two-side closed-rank-j gluing
lemma then completes the original exact source, provided the
source has maximal intrinsic U-size, the sides have <=j actual
vertices, Old has its closed rank-j invariant, and the stated
strong amalgamation/closed heredity hypotheses hold.

This provides an alternate honest closed K-root to fixed A-letter
geometry in all cases where the true separator is already
closed and in K. It does not say arbitrary two-REST core roots
are intrinsically U-closed or members of K; their protected
completion into A can be noninjective. That remains OPEN.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- An ordinary HE on an ORDINARY irreducible full relational
source is necessarily a FULL induced embedding of the source.
This is a useful exact proof interface for compatible K-roots,
rather than a fabricated embedding based solely on part labels. -/
theorem native2019_ordinaryHE_irreducible_root_is_full
    {H V : Type v}
    (Root : RelStructure L H)
    (Old : RelStructure L V)
    (hIrred : Root.Irreducible)
    (f : H → V)
    (hf : Root.IsHomomorphismEmbedding Old f) :
    ∃ a : Embedding Root Old, ∀ x : H, a x = f x := by
  classical
  have hUniv : (Root.induce (Set.univ : Set H)).Irreducible := by
    intro x y hxy
    have hne : x.1 ≠ y.1 := by
      intro hEq
      apply hxy
      apply Subtype.ext
      exact hEq
    obtain ⟨R, z, i, j, hz, hzi, hzj⟩ := hIrred hne
    let zz : Fin (L.arity R) → (Set.univ : Set H) :=
      fun k => ⟨z k, Set.mem_univ (z k)⟩
    refine ⟨R, zz, i, j, ?_, ?_, ?_⟩
    · change Root.rel R (Subtype.val ∘ zz)
      simpa [zz] using hz
    · apply Subtype.ext
      simpa [zz] using hzi
    · apply Subtype.ext
      simpa [zz] using hzj
  obtain ⟨e, he⟩ := hf.embeddingOn Set.univ hUniv
  let u : Embedding Root (Root.induce (Set.univ : Set H)) := {
    toFun := fun x => ⟨x, Set.mem_univ x⟩
    injective := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    map_rel_iff := fun _ _ => Iff.rfl
  }
  let a : Embedding Root Old := e.comp u
  exact ⟨a, fun x => he (u x)⟩

/-- A corrected K-completion of an original maximal-rank
exact weak source follows from a genuine free two-side split
with bounded OLD-projected side ranks, when its literal common
source root is already U-CLOSED and a K-member.

There is NO fixed selected-A word-embedding assumption: the
root K-member supplies its own two full Old embeddings via
ordinary irreducibility. No unproved general-root claim. -/
theorem inducedClosed2019_maximal_weak_two_old_maps_glue_of_closed_K_root
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {H E F C V : Type v}
    [Finite H] [Finite V]
    [Fintype E] [Fintype F] [Fintype C]
    {Root : RelStructure L H}
    {Left : RelStructure L E}
    {Right : RelStructure L F}
    {Whole : RelStructure L C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hMax : USize rules Whole = Fintype.card C)
    (Old : RelStructure L V)
    (hOldClosed : IsUClosed rules Old)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (S : RelStructure L X),
      K S → S.Irreducible)
    (hRootK : K Root)
    (hRootClosed : IsUClosed rules Root)
    (pL : E → V) (pR : F → V)
    (hpL : Left.IsHomomorphismEmbedding Old pL)
    (hpR : Right.IsHomomorphismEmbedding Old pR)
    (rank : ℕ)
    (hSizeL : Fintype.card E ≤ rank)
    (hSizeR : Fintype.card F ≤ rank)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.induce T) →
      USize rules (Old.induce T) ≤ rank →
        HasInducedClosedUKCompletion K rules
          (Old.induce T)) :
    HasInducedClosedUKCompletion K rules Whole := by
  have hRootIrred : Root.Irreducible := hKIrr Root hRootK
  have hfRootL : Root.IsHomomorphismEmbedding Old (pL ∘ sL) :=
    hpL.comp sL.isHomomorphismEmbedding
  have hfRootR : Root.IsHomomorphismEmbedding Old (pR ∘ sR) :=
    hpR.comp sR.isHomomorphismEmbedding
  obtain ⟨aL, haL⟩ :=
    native2019_ordinaryHE_irreducible_root_is_full
      Root Old hRootIrred (pL ∘ sL) hfRootL
  obtain ⟨aR, haR⟩ :=
    native2019_ordinaryHE_irreducible_root_is_full
      Root Old hRootIrred (pR ∘ sR) hfRootR
  exact inducedClosed2019_maximal_weak_two_ordinary_side_maps_via_A
    rules hStrong hHer hKIrr hFree hMax hOldClosed
    hRootK hRootClosed
    (fun x : H => x) pL pR hpL hpR aL aR
    (fun x => (haL x).symm) (fun x => (haR x).symm)
    rank hSizeL hSizeR hOldRank

end AllThoseRamseyClasses.Published
