import AllThoseRamseyClasses.Published.GeneratedClosureProfileBoundary2019
import PartiteConstruction.Ramsey.CopywiseTreeHomomorphism

/-!
# Strict trees of profiled Base have actual finite K-completions

The root of a strict relational tree gluing lies in a full Base copy on
each side. Matching profile records turn that weak root into one actual
closed K-boundary with compatible FULL embeddings. Strong K-amalgamation
then combines the two independent targets. No boundary oracle, native
rank bound, or full hereditary closure of K on weak substructures is
assumed. The output target is a canonical profile expansion of a real
finite K-member.

This supplies the tree-completion part of the alternate main-theorem
route. It does not yet construct its final closed sparse Picture.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A strict tree root factors through an actual full Base copy, with
vertex-exact compatibility on its original weak carrier. -/
theorem strict2019_root_factor_through_base
    {UB H W : Type v}
    (Base : RelStructure L UB) (Root : RelStructure L H) (T : RelStructure L W)
    (hTree : TreeAmalgam Base W T)
    (r : Embedding Root T) (hContainer : r.ContainedInIrreducible) :
    ∃ (b : Embedding Base T) (a : Embedding Root Base),
      ∀ x, r x = b (a x) := by
  classical
  obtain ⟨S, hS, hRange⟩ := hContainer
  obtain ⟨b, hb⟩ := hTree.irreducible_contained_in_copy hS (inclusion T S)
  have hFactor : ∀ x : H, ∃ y : UB, r x = b y := by
    intro x
    exact hb ⟨r x, hRange x⟩
  exact ⟨b, r.factorThroughRange b hFactor,
    fun x => Classical.choose_spec (hFactor x)⟩

/-- A strict tree of canonical profiled Base copies has a finite target
in K preserving all its Base copies. Root K-membership and compatible
FULL closed boundary embeddings are constructed from profile records. -/
theorem closureProfile2019_strict_tree_copywise_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {UB W : Type v} [Finite UB]
    (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base) (hBK : K Base)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X), K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules)
    (hStrong : HasFiniteStrongAmalgamation K)
    (T : RelStructure (closureProfileLanguage2019 rules Base) W)
    (hTree : TreeAmalgam (closureProfileExpansion2019 rules Base Base) W T) :
    ∃ (X : Type v) (_ : Finite X) (E : RelStructure L X),
      K E ∧ ∃ f : W → X,
        CopywiseCompletion (closureProfileExpansion2019 rules Base Base) T
          (closureProfileExpansion2019 rules Base E) f := by
  classical
  have hBIrr : (closureProfileExpansion2019 rules Base Base).Irreducible :=
    (closureProfile2019_base_hereditarily_irreducible Base hBase).irreducible
  induction hTree with
  | @copy Wcopy Tcopy hIso =>
    let e : Embedding (closureProfileExpansion2019 rules Base Base) Tcopy := hIso.toEmbedding
    have hRange : ∀ x : Wcopy, ∃ b : UB, (Embedding.id Tcopy) x = e b := by
      intro x
      exact ⟨hIso.toEquiv.symm x, (hIso.toEquiv.apply_symm_apply x).symm⟩
    let inv : Embedding Tcopy (closureProfileExpansion2019 rules Base Base) :=
      (Embedding.id Tcopy).factorThroughRange e hRange
    exact ⟨UB, inferInstance, Base, hBK, inv,
      fun b => ⟨inv.comp b, fun _ => rfl⟩⟩
  | @glue W1 W2 H W T1 T2 Root Whole
      hTree1 hTree2 sL sR hcL hcR iL iR hFree ihL ihR =>
    obtain ⟨X, hX, E1, hK1, fL, hfL⟩ := ihL
    obtain ⟨Y, hY, E2, hK2, fR, hfR⟩ := ihR
    letI : Finite X := hX
    letI : Finite Y := hY
    obtain ⟨bL, rootB, hFactor⟩ := strict2019_root_factor_through_base
      (closureProfileExpansion2019 rules Base Base) Root T1 hTree1 sL hcL
    letI : Finite H := Finite.of_injective rootB rootB.injective
    letI : Fintype H := Fintype.ofFinite H
    obtain ⟨bTargetL, hbTargetL⟩ := hfL bL
    obtain ⟨rootTargetR, hRootTargetR⟩ :=
      CopywiseCompletion.on_strictRoot hTree2 sR hcR fR hfR
    obtain ⟨Boundary, aL, aR, q, hBoundaryClosed, hBoundaryK, hQL, hQR⟩ :=
      closureProfile2019_common_weak_root_closed_boundary
        Base E2 hBase hBK hHer Root rootB rootTargetR
    let oldBL : Embedding Base E1 := closureProfileForgetEmbedding2019 Base bTargetL
    let boundaryL : Embedding (Base.induce Boundary) E1 := oldBL.comp aL
    have hLeft : ∀ r : H, boundaryL (q r) = fL (sL r) := by
      intro r
      calc
        boundaryL (q r) = bTargetL (rootB r) := congrArg bTargetL (hQL r)
        _ = fL (bL (rootB r)) := hbTargetL (rootB r)
        _ = fL (sL r) := congrArg fL (hFactor r).symm
    have hRight : ∀ r : H, aR (q r) = fR (sR r) := by
      intro r
      exact (hQR r).trans (hRootTargetR r)
    obtain ⟨Z, hZ, E, hKE, jL, jR, hAgree, _⟩ :=
      hStrong (Base.induce Boundary) E1 E2 hBoundaryK hK1 hK2 boundaryL aR
    let jLPlus := closureProfileEmbedding2019 Base jL (hClosed E1 hK1) (hClosed E hKE)
    let jRPlus := closureProfileEmbedding2019 Base jR (hClosed E2 hK2) (hClosed E hKE)
    have hCompat : ∀ r : H, jLPlus (fL (sL r)) = jRPlus (fR (sR r)) := by
      intro r
      change jL (fL (sL r)) = jR (fR (sR r))
      calc
        jL (fL (sL r)) = jL (boundaryL (q r)) := congrArg jL (hLeft r).symm
        _ = jR (aR (q r)) := hAgree (q r)
        _ = jR (fR (sR r)) := congrArg jR (hRight r)
    exact ⟨Z, hZ, E, hKE,
      hFree.compatibleFold (jLPlus ∘ fL) (jRPlus ∘ fR) hCompat,
      CopywiseCompletion.fold_free hBIrr hFree fL fR hfL hfR jLPlus jRPlus hCompat⟩

/-- The constructed map of a strict profile tree is a positive ordinary
homomorphism-embedding: every relation tuple and irreducible test lies
in an actual Base copy. Its target is a canonical expansion of E in K. -/
theorem closureProfile2019_strict_tree_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {UB W : Type v} [Finite UB]
    (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base) (hBK : K Base)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X), K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules) (hStrong : HasFiniteStrongAmalgamation K)
    (T : RelStructure (closureProfileLanguage2019 rules Base) W)
    (hTree : TreeAmalgam (closureProfileExpansion2019 rules Base Base) W T) :
    ∃ (X : Type v) (_ : Finite X) (E : RelStructure L X),
      K E ∧ ∃ f : W → X,
        T.IsHomomorphismEmbedding (closureProfileExpansion2019 rules Base E) f := by
  obtain ⟨X, hX, E, hK, f, hf⟩ :=
    closureProfile2019_strict_tree_copywise_completion
      Base hBase hBK hClosed hHer hStrong T hTree
  exact ⟨X, hX, E, hK, f, hf.toHomomorphismEmbedding_of_strictTree hTree⟩

/-- An arbitrary exact weak source with a strict profile-tree completion
therefore has a genuine finite canonical-profile K-target. -/
theorem closureProfile2019_tree_completion_to_K
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {UB W : Type v} [Finite UB]
    (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base) (hBK : K Base)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X), K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules) (hStrong : HasFiniteStrongAmalgamation K)
    (Source : RelStructure (closureProfileLanguage2019 rules Base) W)
    (hTree : HasTreeCompletion (closureProfileExpansion2019 rules Base Base) Source) :
    ∃ (X : Type v) (_ : Finite X) (E : RelStructure L X),
      K E ∧ ∃ f : W → X,
        Source.IsHomomorphismEmbedding (closureProfileExpansion2019 rules Base E) f := by
  obtain ⟨Y, T, hT, f, hf⟩ := hTree
  obtain ⟨X, hX, E, hK, g, hg⟩ :=
    closureProfile2019_strict_tree_completion Base hBase hBK hClosed hHer hStrong T hT
  exact ⟨X, hX, E, hK, g ∘ f, hg.comp hf⟩

end AllThoseRamseyClasses.Published
