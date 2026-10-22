import AllThoseRamseyClasses.Lifts.GeometricProperSubpiece
import AllThoseRamseyClasses.Lifts.MinimalMixedGeometricPiece

/-!
# Root retention is exactly the missing localization invariant for Claim 2

When a new native functional geometric piece Q is selected
from a previously chosen piece P, the original proof needs
the complete Q piece to be a genuine PROPER sub-piece of P
and, more importantly, its selected nonroot component to
contain strictly fewer SOURCE vertices.

The following bridge derives those conclusions from transparent
source-geometric hypotheses:
* the old closed root of P is RETAINED in the root of Q;
* the full new closed root remains inside P's vertex set;
* the left and right distinguished Q vertices belong to
  P's original selected nonroot component.

Cut monotonicity then makes the Q component a subset of
the old component, and Q's opposite distinguished vertex
witnesses strict containment. No weak target map, canonical
lift, forbidden-family closure or global injectivity occurs.

Consequently, at a smallest mixed piece P, ANY other mixed
piece Q satisfying the latter two hypotheses must LOSE at
least one old root vertex. This is a concrete obstruction,
not an assertion that root retention is automatic.

A reduction in cardinality of Q's root alone gives neither
proper-subpiece containment nor smaller nonroot size.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- Retaining the complete OLD root while keeping the NEW root
inside the old genuine piece localizes the whole NEW selected
component, provided its selected vertex lies in the old
component. The opposite vertex then witnesses a STRICT
proper sub-piece and strictly smaller nonroot component.

The proper-subpiece result concerns the full closed root
together with the selected component, not root width alone. -/
theorem geometricPiece_proper_of_retainedOldRoot
    (A : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData A n)
    (Q : GeometricFunctionalPieceData A m)
    (hRootRetained : Set.range P.roots ⊆ Set.range Q.roots)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices A P)
    (hQleftOld : Q.left.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left)
    (hQrightOld : Q.right.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left) :
    geometricPieceVertices A Q ⊂ geometricPieceVertices A P ∧
    functionalComponentFrom A (Set.range Q.roots) Q.left ⊂
      functionalComponentFrom A (Set.range P.roots) P.left := by
  have hCompSubset :
      functionalComponentFrom A (Set.range Q.roots) Q.left ⊆
        functionalComponentFrom A (Set.range P.roots) P.left := by
    intro z hz
    have hzOld :=
      componentFrom_subset_of_cut_subset
        A.graph hRootRetained Q.left hz
    exact ⟨hzOld.1, hQleftOld.2.trans hzOld.2⟩
  have hQrightNotQ :
      Q.right.1 ∉ functionalComponentFrom A
        (Set.range Q.roots) Q.left := by
    intro hQrightComp
    have hRightEq :
        (⟨Q.right.1, hQrightComp.1⟩ :
          {z : V // z ∉ Set.range Q.roots}) = Q.right :=
      Subtype.ext rfl
    have hPath : ReachOutside A.graph (Set.range Q.roots)
        Q.left Q.right := by
      simpa only [hRightEq] using hQrightComp.2
    exact Q.minimal.2.1 hPath
  have hCompProper :
      functionalComponentFrom A (Set.range Q.roots) Q.left ⊂
        functionalComponentFrom A (Set.range P.roots) P.left := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨hCompSubset, ?_⟩
    intro hEq
    apply hQrightNotQ
    rw [hEq]
    exact hQrightOld
  have hPieceProper :
      geometricPieceVertices A Q ⊂ geometricPieceVertices A P :=
    geometricPiece_proper_subpiece_of_rightInOldComponent
      A P Q hQrootInsideP hCompSubset hQrightOld
  exact ⟨hPieceProper, hCompProper⟩

/-- In a finite source, root retention yields the EXACT strict
nonroot-size decrease used in printed Claim 2, not just a
strict inclusion of complete piece vertices. -/
theorem geometricPiece_strictNonrootCount_of_retainedOldRoot
    [Finite V]
    (A : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData A n)
    (Q : GeometricFunctionalPieceData A m)
    (hRootRetained : Set.range P.roots ⊆ Set.range Q.roots)
    (hQrootInsideP :
      Set.range Q.roots ⊆ geometricPieceVertices A P)
    (hQleftOld : Q.left.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left)
    (hQrightOld : Q.right.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left) :
    (functionalComponentFrom A
      (Set.range Q.roots) Q.left).ncard <
      (functionalComponentFrom A
        (Set.range P.roots) P.left).ncard := by
  exact Set.ncard_lt_ncard
    (geometricPiece_proper_of_retainedOldRoot
      A P Q hRootRetained hQrootInsideP
      hQleftOld hQrightOld).2

/-- At a source-minimal genuinely mixed piece P, an alternative
genuinely mixed piece Q whose entire root remains inside P and
whose two distinguished vertices belong to P's old selected
component MUST OMIT AN ORIGINAL ROOT VERTEX of P.

This is an explicit root-loss WITNESS: it explains why a
smaller-root mixed piece constructed from failed boundary
coverage need not give the printed nonroot-size contradiction. -/
theorem minimalMixedPiece_localCandidate_losesOldRoot
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P Q : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    (hQrootInsideP :
      Set.range Q.data.roots ⊆ geometricPieceVertices Source P.data)
    (hQleftOld : Q.data.left.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld : Q.data.right.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left) :
    ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∉ Set.range Q.data.roots := by
  classical
  by_contra hNoLost
  have hRetained :
      Set.range P.data.roots ⊆ Set.range Q.data.roots := by
    intro r hrP
    by_contra hrNotQ
    exact hNoLost ⟨r, hrP, hrNotQ⟩
  have hProper :=
    (geometricPiece_proper_of_retainedOldRoot
      Source P.data Q.data hRetained
      hQrootInsideP hQleftOld hQrightOld).2
  exact minimalMixedGeometricPiece_no_proper_mixed_component
    P hMinimal Q hProper

end AllThoseRamseyClasses.Lifts
