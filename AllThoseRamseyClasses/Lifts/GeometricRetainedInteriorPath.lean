import AllThoseRamseyClasses.Lifts.GeometricInnerSourceInterface

/-!
# Apply the retained-interior path theorem to an actual selected source

The generic full functional amalgam argument of merged Track A PR #739
carried an explicit source-shape hypothesis:
every Inner-private vertex belongs to the selected U-component D.

For an ACTUAL geometric piece of a forbidden source A, this is
not an extra assumption. The full selected piece is U union the
whole selected component, and `geometricGlobalSource_freeDiagram`
constructs the literal full source amalgam with that piece.

This module discharges that premise and transports the first-U-root
safe path in the new source along the unchanged complete complement.
No root-injectivity of the weak forbidden target map or nestedness
of the old and inner cuts is required. The selected new inner
component must still be attached separately before one obtains
the entire new opposite outer component.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V W : Type} {n : ℕ}

/-- Every retained old outer-interior vertex connected to the
genuine selected geometric inner component outside an arbitrary
older cut has a path in the replacement source from a surviving
inner root vertex.

In contrast to the generic source theorem, `hPrivateInD` is
PROVED here from the real geometric root chart. Only a FULL
embedding of the unchanged complement into New is required.
-/
theorem geometricGlobalSource_retainedInterior_has_newRootPath
    (A : Structure L V)
    (d : GeometricFunctionalPieceData A n)
    (New : Structure L W)
    (jComp : Structure.Embedding
      (geometricGlobalComplementChart A d).str New)
    (T : Set (geometricGlobalComplementChart A d).Carrier)
    (x : {w : V // w ∉
      (functionalComponentComplementEmbedding A (Set.range d.roots)
          d.minimal.1 d.left) '' T})
    (hx :
      x.1 ∈ componentFrom A.graph (Set.range d.roots) d.left)
    (y : {b : (geometricGlobalComplementChart A d).Carrier // b ∉ T})
    (hyRetained :
      (functionalComponentComplementEmbedding A (Set.range d.roots)
          d.minimal.1 d.left) y.1 ∉
        componentFrom A.graph (Set.range d.roots) d.left)
    (hOldPath : ReachOutside A.graph
      ((functionalComponentComplementEmbedding A (Set.range d.roots)
          d.minimal.1 d.left) '' T)
      x
      (fullFunctionalEmbedding_outsideCut
        (functionalComponentComplementEmbedding A (Set.range d.roots)
            d.minimal.1 d.left) T y)) :
    ∃ r : {b : (geometricGlobalComplementChart A d).Carrier // b ∉ T},
      r.1 ∈ Set.range (geometricGlobalComplementChart A d).rootEmbedding ∧
      ReachOutside New.graph (jComp '' T)
        (fullFunctionalEmbedding_outsideCut jComp T r)
        (fullFunctionalEmbedding_outsideCut jComp T y) := by
  let Comp := geometricGlobalComplementChart A d
  let oldComp : Structure.Embedding Comp.str A :=
    functionalComponentComplementEmbedding A (Set.range d.roots)
      d.minimal.1 d.left
  let U : Set V := oldComp '' Set.range Comp.rootEmbedding
  have hU : U = Set.range d.roots :=
    geometricGlobalSource_innerRoot_range_eq A d
  let inner : {w : V // w ∉ U} := ⟨d.left.1, by
    rw [hU]
    exact d.left.2⟩
  have hPrivate :
      ∀ e : (geometricGlobalFunctionalChart A d).ext.Carrier,
        e ∉ Set.range
          (geometricGlobalFunctionalChart A d).ext.rootEmbedding →
        (functionalComponentEmbedding A (Set.range d.roots)
            d.minimal.1 d.left) e ∈
          componentFrom A.graph U inner := by
    intro e he
    have hh :=
      geometricGlobalSource_innerPrivate_in_selectedComponent A d e he
    change e.1 ∈ componentFrom A.graph U inner
    rw [hU]
    exact hh
  have hxU : x.1 ∈ componentFrom A.graph U inner := by
    change x.1 ∈ componentFrom A.graph U inner
    rw [hU]
    exact hx
  have hyU :
      oldComp y.1 ∉ componentFrom A.graph U inner := by
    change oldComp y.1 ∉ componentFrom A.graph U inner
    rw [hU]
    exact hyRetained
  exact fullFreeAmalgam_retainedInterior_has_newRootPath
    (geometricGlobalSource_freeDiagram A d)
    jComp T inner hPrivate x hxU y hyU hOldPath

end AllThoseRamseyClasses.Lifts
