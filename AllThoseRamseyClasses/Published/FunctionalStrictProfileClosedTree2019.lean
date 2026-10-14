import AllThoseRamseyClasses.Published.FunctionalStrictProfileRoot2019
import AllThoseRamseyClasses.Published.FunctionalClosedStrictTree2019
import AllThoseRamseyClasses.Published.ProfileStrictTreeCompletion2019
import PartiteConstruction.Iterated.FreeAmalgam
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-!
# Strict profiled Base trees complete into actual U-closed strict Base trees

Unlike the existing completion into an arbitrary strong-amalgamation class,
this construction freely glues actual U-closed trees of Base copies.
At a weak profiled overlap it takes the *shared actual closed hull*
inside one Base copy on each side, before amalgamating.

The produced target is itself a strict tree of copies of Base.  Both
side maps into the free amalgam remain full embeddings, the gluing
root lies inside actual Base copies, and the final map preserves
every controlled profile Base copy.

This records closure of every intermediate/root, supplying the tree core of the
native partial-function strict sparsening theorem.  Its transfer
to primitive function semantics is a separate obligation.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- The target of a strict profile Base-tree may be chosen to be a
genuine strict tree of U-closed original Base copies, not just an
arbitrary finite strong-amalgamation target.

The ordinary irreducibility assumption on Base ensures the enlarged
U-closed gluing roots are contained in irreducible Base copies.
For ordered finite models this is automatic. -/
theorem closureProfile2019_strict_tree_closedRoot_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {UB W : Type v} [Finite UB]
    (Base : RelStructure L UB)
    (hBaseClosed : IsUClosed rules Base)
    (hBaseIrred : Base.Irreducible)
    (hBK : K Base)
    (hHer : ClosedUHereditary K rules)
    (T : RelStructure (closureProfileLanguage2019 rules Base) W)
    (hTree : TreeAmalgam (closureProfileExpansion2019 rules Base Base) W T) :
    ∃ (X : Type v) (_ : Finite X) (Target : RelStructure L X),
      UClosedStrictTreeAmalgam rules Base X Target ∧
      ∃ f : W → X,
        CopywiseCompletion (closureProfileExpansion2019 rules Base Base)
          T (closureProfileExpansion2019 rules Base Target) f := by
  classical
  have hBPlusIrred :
      (closureProfileExpansion2019 rules Base Base).Irreducible :=
    (closureProfile2019_base_hereditarily_irreducible Base hBaseClosed).irreducible
  induction hTree with
  | @copy Wcopy Tcopy hIso =>
    let b : Embedding (closureProfileExpansion2019 rules Base Base) Tcopy :=
      hIso.toEmbedding
    have hRange : ∀ x : Wcopy, ∃ a : UB, (Embedding.id Tcopy) x = b a := by
      intro x
      exact ⟨hIso.toEquiv.symm x, (hIso.toEquiv.apply_symm_apply x).symm⟩
    let inv : Embedding Tcopy (closureProfileExpansion2019 rules Base Base) :=
      (Embedding.id Tcopy).factorThroughRange b hRange
    refine ⟨UB, inferInstance, Base,
      UClosedStrictTreeAmalgam.copy (Iso.refl Base) hBaseClosed, inv, ?_⟩
    intro bcopy
    exact ⟨inv.comp bcopy, fun _ => rfl⟩
  | @glue W1 W2 H W T1 T2 Root Whole
      hTree1 hTree2 sL sR hcL hcR iL iR hFree ihL ihR =>
    obtain ⟨X, hX, E1, hTargetTreeL, fL, hfL⟩ := ihL
    obtain ⟨Y, hY, E2, hTargetTreeR, fR, hfR⟩ := ihR
    have hE1Closed : IsUClosed rules E1 := hTargetTreeL.isUClosed
    have hE2Closed : IsUClosed rules E2 := hTargetTreeR.isUClosed
    letI : Finite X := hX
    letI : Finite Y := hY
    obtain ⟨bL, rootBL, hFactorL⟩ := strict2019_root_factor_through_base
      (closureProfileExpansion2019 rules Base Base) Root T1 hTree1 sL hcL
    obtain ⟨bR, rootBR, hFactorR⟩ := strict2019_root_factor_through_base
      (closureProfileExpansion2019 rules Base Base) Root T2 hTree2 sR hcR
    letI : Finite H := Finite.of_injective rootBL rootBL.injective
    letI : Fintype H := Fintype.ofFinite H
    obtain ⟨bTargetL, hbTargetL⟩ := hfL bL
    obtain ⟨bTargetR, hbTargetR⟩ := hfR bR
    obtain ⟨S, aBL, aBR, q, hSClosed, _hSK, hQL, hQR⟩ :=
      closureProfile2019_common_weak_root_closed_boundary
        Base Base hBaseClosed hBK hHer Root rootBL rootBR
    let oldBL : Embedding Base E1 :=
      closureProfileForgetEmbedding2019 Base bTargetL
    let oldBR : Embedding Base E2 :=
      closureProfileForgetEmbedding2019 Base bTargetR
    let targetL : Embedding (Base.induce S) E1 := oldBL.comp aBL
    let targetR : Embedding (Base.induce S) E2 := oldBR.comp aBR
    have hLeft : ∀ h : H, targetL (q h) = fL (sL h) := by
      intro h
      calc
        targetL (q h) = bTargetL (rootBL h) :=
          congrArg bTargetL (hQL h)
        _ = fL (bL (rootBL h)) := hbTargetL (rootBL h)
        _ = fL (sL h) := congrArg fL (hFactorL h).symm
    have hRight : ∀ h : H, targetR (q h) = fR (sR h) := by
      intro h
      calc
        targetR (q h) = bTargetR (rootBR h) :=
          congrArg bTargetR (hQR h)
        _ = fR (bR (rootBR h)) := hbTargetR (rootBR h)
        _ = fR (sR h) := congrArg fR (hFactorR h).symm
    have hContainL : targetL.ContainedInIrreducible := by
      apply Embedding.containedInIrreducible_of_range_subset
        hBaseIrred oldBL targetL
      intro s
      exact ⟨aBL s, rfl⟩
    have hContainR : targetR.ContainedInIrreducible := by
      apply Embedding.containedInIrreducible_of_range_subset
        hBaseIrred oldBR targetR
      intro s
      exact ⟨aBR s, rfl⟩
    let Target := FreeAmalgam.amalgam
      (Base.induce S) E1 E2 targetL targetR
    let jL := FreeAmalgam.leftEmbedding
      (Base.induce S) E1 E2 targetL targetR
    let jR := FreeAmalgam.rightEmbedding
      (Base.induce S) E1 E2 targetL targetR
    have hTargetFree : IsFreeAmalgam targetL targetR jL jR :=
      FreeAmalgam.isFreeAmalgam
        (Base.induce S) E1 E2 targetL targetR
    have hTargetClosed : IsUClosed rules Target :=
      hTargetFree.isUClosed hSClosed hE1Closed hE2Closed
    have hTargetStrict : UClosedStrictTreeAmalgam rules Base
        (FreeAmalgam.Vertex (Base.induce S) E1 E2 targetL targetR) Target :=
      UClosedStrictTreeAmalgam.glue
        hTargetTreeL hTargetTreeR hSClosed
        targetL targetR hContainL hContainR jL jR hTargetFree
    let jLPlus := closureProfileEmbedding2019 Base jL hE1Closed hTargetClosed
    let jRPlus := closureProfileEmbedding2019 Base jR hE2Closed hTargetClosed
    have hCompat : ∀ h : H, jLPlus (fL (sL h)) = jRPlus (fR (sR h)) := by
      intro h
      change jL (fL (sL h)) = jR (fR (sR h))
      calc
        jL (fL (sL h)) = jL (targetL (q h)) :=
          congrArg jL (hLeft h).symm
        _ = jR (targetR (q h)) :=
          FreeAmalgam.left_right_overlap
            (Base.induce S) E1 E2 targetL targetR (q h)
        _ = jR (fR (sR h)) :=
          congrArg jR (hRight h)
    refine ⟨_, inferInstance, Target, hTargetStrict, ?_, ?_⟩
    · exact hFree.compatibleFold
        (jLPlus ∘ fL) (jRPlus ∘ fR) hCompat
    · exact CopywiseCompletion.fold_free
        hBPlusIrred hFree fL fR hfL hfR jLPlus jRPlus hCompat

end AllThoseRamseyClasses.Published
