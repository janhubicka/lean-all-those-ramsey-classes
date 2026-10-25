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

/-- If the selected component of Q starts inside P's selected
component but subsequently escapes it, the path MUST pass
through an original separator-root vertex of P. That vertex
then belongs to Q's complete selected nonroot component.

This is an ACTUAL path/connectedness result in the original
functional Gaifman graph, not a weak-image or quotient claim.
No relation between the two selected root tuples is assumed. -/
theorem geometricPiece_escapingComponent_capturesOldRoot
    (A : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData A n)
    (Q : GeometricFunctionalPieceData A m)
    (hQleftOld : Q.left.1 ∈ functionalComponentFrom A
      (Set.range P.roots) P.left)
    (hEscapes :
      ¬ functionalComponentFrom A (Set.range Q.roots) Q.left ⊆
          functionalComponentFrom A (Set.range P.roots) P.left) :
    ∃ r : V,
      r ∈ Set.range P.roots ∧
      r ∈ functionalComponentFrom A
        (Set.range Q.roots) Q.left := by
  classical
  by_contra hNoRoot
  have hAvoidOldRoot : ∀ r : V,
      r ∈ Set.range P.roots →
      r ∉ functionalComponentFrom A
        (Set.range Q.roots) Q.left := by
    intro r hrOld hrNew
    exact hNoRoot ⟨r, hrOld, hrNew⟩
  have hLift :
      ∀ (v : {z : V // z ∉ Set.range Q.roots}),
        ReachOutside A.graph (Set.range Q.roots) Q.left v →
        v.1 ∈ functionalComponentFrom A
          (Set.range P.roots) P.left := by
    intro v hPath
    induction hPath with
    | refl =>
        exact hQleftOld
    | @tail a b hab hedge ih =>
        have hbNew :
            b.1 ∈ functionalComponentFrom A
              (Set.range Q.roots) Q.left :=
          ⟨b.2, hab.tail hedge⟩
        have hbNotOldRoot : b.1 ∉ Set.range P.roots := by
          intro hbRoot
          exact hAvoidOldRoot b.1 hbRoot hbNew
        exact componentFrom_step A.graph
          (Set.range P.roots) P.left
          ih hbNotOldRoot hedge
  apply hEscapes
  intro z hzNew
  exact hLift ⟨z, hzNew.1⟩ hzNew.2

/-- For a genuinely NONROOT-size-minimal mixed piece P, any
other mixed piece Q whose two distinguished vertices are in
P's selected component must CAPTURE an old separator-root
vertex INSIDE Q's selected nonroot component.

This strengthens mere root loss: the lost old root has a
specific geometric role, providing an escape path from P's
selected component. No new-root containment or target map
injectivity hypothesis is required. -/
theorem minimalMixedPiece_otherMixed_capturesOldRoot
    [Finite V]
    (Source : Structure L V)
    (S AOnly BOnly : Set V)
    (P Q : MixedGeometricPiece Source S AOnly BOnly)
    (hMinimal : ∀ D : MixedGeometricPiece Source S AOnly BOnly,
      P.nonrootCount ≤ D.nonrootCount)
    (hQleftOld : Q.data.left.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left)
    (hQrightOld : Q.data.right.1 ∈
      functionalComponentFrom Source
        (Set.range P.data.roots) P.data.left) :
    ∃ r : V,
      r ∈ Set.range P.data.roots ∧
      r ∈ functionalComponentFrom Source
        (Set.range Q.data.roots) Q.data.left := by
  have hQrightNotNew :
      Q.data.right.1 ∉ functionalComponentFrom Source
        (Set.range Q.data.roots) Q.data.left := by
    intro hz
    have hRightEq :
        (⟨Q.data.right.1, hz.1⟩ :
          {z : V // z ∉ Set.range Q.data.roots}) = Q.data.right :=
      Subtype.ext rfl
    have hPath : ReachOutside Source.graph
        (Set.range Q.data.roots) Q.data.left Q.data.right := by
      simpa only [hRightEq] using hz.2
    exact Q.data.minimal.2.1 hPath
  have hNotSubset :
      ¬ functionalComponentFrom Source
          (Set.range Q.data.roots) Q.data.left ⊆
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
    intro hSub
    have hProper :
        functionalComponentFrom Source
          (Set.range Q.data.roots) Q.data.left ⊂
        functionalComponentFrom Source
          (Set.range P.data.roots) P.data.left := by
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hSub, ?_⟩
      intro hEq
      apply hQrightNotNew
      rw [hEq]
      exact hQrightOld
    exact minimalMixedGeometricPiece_no_proper_mixed_component
      P hMinimal Q hProper
  exact geometricPiece_escapingComponent_capturesOldRoot
    Source P.data Q.data hQleftOld hNotSubset

end AllThoseRamseyClasses.Lifts
