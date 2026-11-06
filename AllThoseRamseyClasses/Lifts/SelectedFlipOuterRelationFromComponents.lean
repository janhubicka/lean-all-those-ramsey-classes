import AllThoseRamseyClasses.Lifts.SelectedGeometricFlipOuterTargetRelation
import AllThoseRamseyClasses.Lifts.GeometricTransportedContextExactCarrier

/-!
# Original outer global relation from ACTUAL component transport

Previously, the selected-Q original outer target relation needed
`hExactContext`: literal equality of the new transported context
with the complete old-root image plus a new outside-root component.

This theorem DERIVES that equality via the checked geometric
source-context lemma. Its inputs instead are three local facts
about the actual original/replacement full functional amalgams:

1. membership of ALL retained complement vertices in the old
   outer component is equivalent to membership in the new one;
2. every inserted Q-private vertex belongs to that new component;
3. each surviving shared inner-root vertex attaches to it.

Those facts are studied independently in Track A, and the complete
old/new contextual carrier equation is not assumed as a premise.

Both whole function-generated boundary equalities and separation
of an opposite component remain EXPLICIT, as does injectivity of
the transported old outer-root tuple under the EHN weak map.
The theorem concludes that the actual TARGET canonical lift
realizes the ORIGINAL global forbidden-piece relation.

This is not unconditional Claim 2, nor strong amalgamation. It uses
the REAL selected finite Q certificate and fixed-root canonical
gluing equivalence, not an arbitrary profile-equivalent extension.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The selected genuine inner flip preserves the original outer
canonical relation in the actual weak target, without assuming the
entire transported context is one new root-plus-component.

Its carrier equality is a CONCLUSION of the smaller, explicit
retained-component, inserted-private and common-root attachment
hypotheses. The two generated boundaries and opposite component
are still necessary extra geometric premises. -/
theorem selectedFlip_originalOuterRelation_of_componentTransport
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W UT : Type} [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old d).root
        (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m)
    (hEqGlue : (functionalRootPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iNewE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iNewE)
    (xNew : {w : W // w ∉
      iNewE '' ((functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
          Set.range P.roots)})
    (hRetained : ∀ b :
      (geometricGlobalComplementChart Old d).Carrier,
      b ∉ ((functionalComponentComplementEmbedding Old
        (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
          Set.range P.roots) →
      ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) b ∈
        componentFrom Old.graph (Set.range P.roots) P.left ↔
       iNewE b ∈ componentFrom New.graph
         (iNewE '' ((functionalComponentComplementEmbedding Old
           (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
             Set.range P.roots)) xNew))
    (hQPrivate : ∀ q : Q.Carrier,
      q ∉ Set.range Q.rootEmbedding →
      iQ q ∈ componentFrom New.graph
        (iNewE '' ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
            Set.range P.roots)) xNew)
    (hRootAttached : ∀ r : Fin m,
      (geometricGlobalComplementChart Old d).rootEmbedding r ∉
        ((functionalComponentComplementEmbedding Old
          (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
            Set.range P.roots) →
      iNewE ((geometricGlobalComplementChart Old d).rootEmbedding r) ∈
        componentFrom New.graph
          (iNewE '' ((functionalComponentComplementEmbedding Old
            (Set.range d.roots) d.minimal.1 d.left) ⁻¹'
              Set.range P.roots)) xNew)
    (x : {w : W // w ∉ Set.range
      (fun i : Fin n => iNewE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))})
    (hX : x.1 = xNew.1)
    (y : {w : W // w ∉ Set.range
      (fun i : Fin n => iNewE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))})
    (hSeparated : ¬ ReachOutside New.graph
      (Set.range (fun i : Fin n => iNewE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))) x y)
    (hLeftBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph
            (Set.range (fun i : Fin n => iNewE
              (⟨P.roots i, hOuterRootOutside i⟩ :
                (geometricGlobalComplementChart Old d).Carrier))) x)) =
          Set.range (fun i : Fin n => iNewE
            (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Old d).Carrier)))
    (hRightBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph
            (Set.range (fun i : Fin n => iNewE
              (⟨P.roots i, hOuterRootOutside i⟩ :
                (geometricGlobalComplementChart Old d).Carrier))) y)) =
          Set.range (fun i : Fin n => iNewE
            (⟨P.roots i, hOuterRootOutside i⟩ :
              (geometricGlobalComplementChart Old d).Carrier)))
    (hn : 0 < n)
    (Target : Structure L UT)
    (flip : W → UT)
    (hFlipWeak : New.IsEHNHomomorphismEmbedding Target flip)
    (hTargetRootInjective :
      Function.Injective (fun i : Fin n =>
        flip (iNewE
          (⟨P.roots i, hOuterRootOutside i⟩ :
            (geometricGlobalComplementChart Old d).Carrier)))) :
    (globalFunctionalCanonicalLift F Target).rel
      (.inr (geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld P hn))
      (fun i : Fin n => flip (iNewE
        (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))) := by
  classical
  let roots : Fin n → W := fun i =>
    iNewE (⟨P.roots i, hOuterRootOutside i⟩ :
      (geometricGlobalComplementChart Old d).Carrier)
  obtain ⟨x', hx', hExactContext'⟩ :=
    geometricTransportedContext_eq_root_union_newComponent
      Old P d hOuterRootOutside Q New iQ iNewE hFree
      xNew hRetained hQPrivate hRootAttached
  have hSameX : x' = x := by
    apply Subtype.ext
    exact hx'.trans hX.symm
  have hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iNewE '' (oldOuterContextInInnerComplement Old P d)) =
      Set.range roots ∪
        componentFrom New.graph (Set.range roots) x := by
    simpa only [hSameX] using hExactContext'
  exact selectedGeometricFlip_preserves_originalOuterRelation
    F Old hFOld P d hInnerRoot hInnerComponent
    hOuterRootOutside Q hSelected hEqGlue
    New hFNew iQ iNewE hFree
    roots (by intro i; rfl) x y hSeparated
    hLeftBoundary hRightBoundary hExactContext hn
    Target flip hFlipWeak hTargetRootInjective

end AllThoseRamseyClasses.Lifts
