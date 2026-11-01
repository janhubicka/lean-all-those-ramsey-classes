import AllThoseRamseyClasses.Lifts.SafeComplementPathTransfer
import AllThoseRamseyClasses.Lifts.InnerRootSafePathSelection

/-!
# Retained outer-interior paths in an actual functional source flip

Let Old = Inner +_Root Complement be a genuine FULL native
functional free amalgam, and let New contain another FULL embedding
of the identical complement. The inner cut U and the older outer
cut iComp(T) need not be nested.

The previous two source proofs provide (a) a first-U-hitting safe
path in Old and (b) edge reflection from Old to Complement whenever
at least one endpoint is outside U. This module combines them,
including the nontrivial change of vertex carriers: a retained
Old vertex is identified with the UNIQUE corresponding complement
vertex through the full source embedding, not through the weak
forbidden-target homomorphism.

The selected inner component is required to contain all old
inner-private source vertices, as is the case for an actual selected
single-component geometric piece. This hypothesis is a SOURCE-side
geometric claim, not forbidden-image injectivity, rooted-profile
agreement, or an assumption that the outer component survives.

What this proves: every retained vertex reachable from the removed
inner component outside an arbitrary old cut T has a transported
path from some surviving inner-root vertex in New.

What remains: identify the new inner component and its root
attachment in the literal replacement diagram, derive equality
of the new opposite generated boundary with the OLD outer root,
and recover the genuine outer minimal-separator piece.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- If the entire private Inner side belongs to its selected U-component,
all Old vertices outside that component are in the exact full Complement.
This uses the free-amalgam cover, overlap, and commutation, not a
noninjective EHN map into a forbidden target. -/
theorem fullFreeAmalgam_outside_innerComponent_in_complement
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Old}
    {iComp : Structure.Embedding Complement Old}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (d : {w : W // w ∉ iComp '' Set.range sComp})
    (hPrivateInD :
      ∀ e : E, e ∉ Set.range sInner →
        iInner e ∈ componentFrom Old.graph
          (iComp '' Set.range sComp) d)
    (w : W)
    (hw : w ∉ componentFrom Old.graph
      (iComp '' Set.range sComp) d) :
    w ∈ Set.range iComp := by
  rcases hFree.covers w with ⟨e, hew⟩ | ⟨b, hbw⟩
  · by_cases heRoot : e ∈ Set.range sInner
    · obtain ⟨r, hr⟩ := heRoot
      refine ⟨sComp r, ?_⟩
      calc
        iComp (sComp r) = iInner (sInner r) :=
          ((hFree.overlap (sInner r) (sComp r)).mpr
            ⟨r, rfl, rfl⟩).symm
        _ = iInner e := congrArg iInner hr
        _ = w := hew.symm
    · exact False.elim (hw (hew ▸ hPrivateInD e heRoot))
  · exact ⟨b, hbw.symm⟩

/-- Source-geometric first-root attachment under a LITERAL full
functional inner replacement.

An old T-avoiding path from the selected inner U-component to a
retained complement vertex need not survive edge-for-edge:
some edges between two U-root vertices can use deleted tuples.
The first-root path is selected with exactly the safe private-endpoint
property, and ONLY those reflected edges are mapped to the new source.

The witness is a genuine surviving complement-root vertex, and the
conclusion is an actual path in New outside the *whole* transported T.
There is no inclusion condition between T and U, no finiteness or
root-image injection assumption, and no claim yet that the new
opposite component has complete generated boundary T. -/
theorem fullFreeAmalgam_retainedInterior_has_newRootPath
    {H E B W W' : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Old}
    {iComp : Structure.Embedding Complement Old}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (jComp : Structure.Embedding Complement New)
    (T : Set B)
    (d : {w : W // w ∉ iComp '' Set.range sComp})
    (hPrivateInD :
      ∀ e : E, e ∉ Set.range sInner →
        iInner e ∈ componentFrom Old.graph
          (iComp '' Set.range sComp) d)
    (x : {w : W // w ∉ iComp '' T})
    (hx : x.1 ∈ componentFrom Old.graph
      (iComp '' Set.range sComp) d)
    (y : {b : B // b ∉ T})
    (hyRetained :
      iComp y.1 ∉ componentFrom Old.graph
        (iComp '' Set.range sComp) d)
    (hOldReach : ReachOutside Old.graph (iComp '' T)
      x (fullFunctionalEmbedding_outsideCut iComp T y)) :
    ∃ r : {b : B // b ∉ T},
      r.1 ∈ Set.range sComp ∧
      ReachOutside New.graph (jComp '' T)
        (fullFunctionalEmbedding_outsideCut jComp T r)
        (fullFunctionalEmbedding_outsideCut jComp T y) := by
  classical
  let U : Set W := iComp '' Set.range sComp
  let D : Set W := componentFrom Old.graph U d
  have hRetained (z : W) (hz : z ∉ D) : z ∈ Set.range iComp :=
    fullFreeAmalgam_outside_innerComponent_in_complement
      hFree d hPrivateInD z hz
  let yOld : {w : W // w ∉ iComp '' T} :=
    fullFunctionalEmbedding_outsideCut iComp T y
  obtain ⟨rOld, hrU, hrSafe⟩ :=
    reachOutside_retainedVertex_safeRootPath
      Old.graph (iComp '' T) U d x yOld
      hx hOldReach hyRetained
  obtain ⟨rComp, hrCompRoot, hrMap⟩ := hrU
  obtain ⟨rIndex, hrIndex⟩ := hrCompRoot
  have hrNotT : rComp ∉ T := by
    intro hT
    exact rOld.2 ⟨rComp, hT, hrMap⟩
  let r : {b : B // b ∉ T} := ⟨rComp, hrNotT⟩
  have hLiftSafe :
      ∀ {a b : {w : W // w ∉ iComp '' T}},
        Relation.ReflTransGen
          (innerRootSafeOutsideAdjacency
            Old.graph (iComp '' T) U d) a b →
        ∀ (pa : {b : B // b ∉ T}),
          iComp pa.1 = a.1 →
          ∃ pb : {b : B // b ∉ T},
            iComp pb.1 = b.1 ∧
            ReachOutside New.graph (jComp '' T)
              (fullFunctionalEmbedding_outsideCut jComp T pa)
              (fullFunctionalEmbedding_outsideCut jComp T pb) := by
    intro a b h
    induction h with
    | refl =>
        intro pa hpa
        exact ⟨pa, hpa, Relation.ReflTransGen.refl⟩
    | @tail a b hpath hedge ih =>
        intro pa hpa
        obtain ⟨pb, hpb, hpathNew⟩ := ih pa hpa
        change a.1 ∉ D ∧ b.1 ∉ D ∧
          (a.1 ∉ U ∨ b.1 ∉ U) ∧
          GaifmanAdjacent Old.graph a.1 b.1 at hedge
        obtain ⟨_, hbNotD, hPrivateU, hEdgeOld⟩ := hedge
        obtain ⟨c, hc⟩ := hRetained b.1 hbNotD
        have hcNotT : c ∉ T := by
          intro hcT
          exact b.2 ⟨c, hcT, hc⟩
        let pc : {b : B // b ∉ T} := ⟨c, hcNotT⟩
        have hPrivateB :
            pb.1 ∉ Set.range sComp ∨ pc.1 ∉ Set.range sComp := by
          rcases hPrivateU with haU | hbU
          · left
            intro hbRoot
            exact haU ⟨pb.1, hbRoot, hpb⟩
          · right
            intro hcRoot
            exact hbU ⟨pc.1, hcRoot, hc⟩
        have hEdge :
            GaifmanAdjacent Old.graph (iComp pb.1) (iComp pc.1) := by
          change GaifmanAdjacent Old.graph (iComp pb.1) (iComp c)
          rw [hpb, hc]
          exact hEdgeOld
        have hNewEdge :
            GaifmanAdjacent New.graph (jComp pb.1) (jComp pc.1) :=
          fullFunctionalEmbedding_gaifmanEdge_map jComp
            (fullFreeAmalgam_safeComplementEdge_reflect
              hFree pb.1 pc.1 hPrivateB hEdge)
        have hNewStep :
            outsideAdjacency New.graph (jComp '' T)
              (fullFunctionalEmbedding_outsideCut jComp T pb)
              (fullFunctionalEmbedding_outsideCut jComp T pc) := hNewEdge
        exact ⟨pc, hc, hpathNew.tail hNewStep⟩
  obtain ⟨last, hLast, hNewPath⟩ :=
    hLiftSafe hrSafe r hrMap
  have hLastEq : last = y := by
    apply Subtype.ext
    apply iComp.injective
    exact hLast
  refine ⟨r, ⟨rIndex, hrIndex⟩, ?_⟩
  simpa only [hLastEq] using hNewPath

/-- If every surviving inner-root vertex is already attached to a
specified new outer-T component, then EVERY old outer-interior vertex
outside the removed inner component that was reachable from it through
Old\\T is now in that same new outer-T component. All paths used are
genuine native full-functional source paths.

This deliberately packages the root-attachment fact separately:
for a selected new geometric inner piece it follows from the
verified `minimalInnerPiece_survivesOuterCut_withWholeGeneratedRoot`,
once the actual new-piece and old-cut data are identified. -/
theorem fullFreeAmalgam_retainedInterior_attaches_to_newOuterComponent
    {H E B W W' : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Old}
    {iComp : Structure.Embedding Complement Old}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (jComp : Structure.Embedding Complement New)
    (T : Set B)
    (d : {w : W // w ∉ iComp '' Set.range sComp})
    (hPrivateInD :
      ∀ e : E, e ∉ Set.range sInner →
        iInner e ∈ componentFrom Old.graph
          (iComp '' Set.range sComp) d)
    (x : {w : W // w ∉ iComp '' T})
    (hx : x.1 ∈ componentFrom Old.graph
      (iComp '' Set.range sComp) d)
    (zNew : {w : W' // w ∉ jComp '' T})
    (hRootAttach :
      ∀ r : {b : B // b ∉ T},
        r.1 ∈ Set.range sComp →
        jComp r.1 ∈ componentFrom New.graph (jComp '' T) zNew)
    (y : {b : B // b ∉ T})
    (hyRetained :
      iComp y.1 ∉ componentFrom Old.graph
        (iComp '' Set.range sComp) d)
    (hOldReach : ReachOutside Old.graph (iComp '' T)
      x (fullFunctionalEmbedding_outsideCut iComp T y)) :
    jComp y.1 ∈ componentFrom New.graph (jComp '' T) zNew := by
  obtain ⟨r, hrRoot, hFromRoot⟩ :=
    fullFreeAmalgam_retainedInterior_has_newRootPath
      hFree jComp T d hPrivateInD
      x hx y hyRetained hOldReach
  obtain ⟨_, hToRoot⟩ := hRootAttach r hrRoot
  exact ⟨(fullFunctionalEmbedding_outsideCut jComp T y).2,
    hToRoot.trans hFromRoot⟩

end AllThoseRamseyClasses.Lifts
