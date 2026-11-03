import AllThoseRamseyClasses.Lifts.FullFreeAmalgamNewOuterConfinement
import AllThoseRamseyClasses.Lifts.RetainedInteriorRootPath

/-!
# Retained private outer-component membership is invariant under a full inner replacement

Two native full functional free amalgams share exactly the same
complete right-hand complement:
  Old = OldInner +_Root Complement
  New = NewInner +_Root Complement.

The common root U need not be comparable with the older cut T of
the retained complement. Under the TRUE source-geometric assumption
that OldInner contains one selected component D of Old outside U,
and both old/new surviving root vertices are attached to the
respective older-T components, membership of a complement-private
vertex in the outer component is equivalent before and after the flip.

The forward direction invokes the verified tuple-safe first-root
transport (#739). The reverse direction uses the true functional
no-escape theorem (#751). The extra old "retained vertex" hypothesis
from #739 is eliminated by the no-cross-component lemma proved here
from whole-tuple side localization of the full native amalgam.

This theorem asserts no complete generated-boundary equality and no
all-test rooted incompatibility-profile congruence. Weak forbidden
target maps play no role; all carrier maps are FULL source embeddings.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A vertex private to the LEFT component in a full functional
amalgam has no Gaifman neighbour outside the left side. Every
higher-arity function incidence tuple is localized to one side. -/
theorem fullFreeAmalgam_leftPrivate_neighbor_in_left
    {H E B W : Type v}
    {Root : Structure L H}
    {Inner : Structure L E}
    {Complement : Structure L B}
    {Whole : Structure L W}
    {sInner : Structure.Embedding Root Inner}
    {sComp : Structure.Embedding Root Complement}
    {iInner : Structure.Embedding Inner Whole}
    {iComp : Structure.Embedding Complement Whole}
    (hFree : Structure.IsFreeAmalgam sInner sComp iInner iComp)
    (e : E) (hePrivate : e ∉ Set.range sInner)
    (w : W)
    (hEdge : GaifmanAdjacent Whole.graph (iInner e) w) :
    w ∈ Set.range iInner := by
  rcases hEdge with ⟨_, sym, xs, j, k, htuple, hj, hk⟩
  rcases functionalFreeAmalgam_graphTuple_side hFree sym xs htuple with
    hLeft | hRight
  · obtain ⟨e', he'⟩ := hLeft k
    exact ⟨e', he'.symm.trans hk⟩
  · obtain ⟨b, hb⟩ := hRight j
    have hOverlap : iInner e = iComp b := hj.symm.trans hb
    obtain ⟨r, hrInner, _⟩ := (hFree.overlap e b).mp hOverlap
    exact False.elim (hePrivate ⟨r, hrInner.symm⟩)

/-- An entire Gaifman component of Old outside the common inner
root, starting in the inner-private side, contains NO vertex
private to the unchanged complement.

In particular the retained-right-private condition used in #739
is automatic for an actual selected inner source component. -/
theorem fullFreeAmalgam_innerComponent_avoids_rightPrivate
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
    (hdInner : d.1 ∈ Set.range iInner)
    (b : B) (hbPrivate : b ∉ Set.range sComp) :
    iComp b ∉ componentFrom Old.graph
      (iComp '' Set.range sComp) d := by
  let U : Set W := iComp '' Set.range sComp
  have hStay :
      ∀ x : {w : W // w ∉ U},
        ReachOutside Old.graph U d x → x.1 ∈ Set.range iInner := by
    intro x hPath
    induction hPath with
    | refl => exact hdInner
    | @tail a c hpre hedge ih =>
        obtain ⟨e, he⟩ := ih
        have hePrivate : e ∉ Set.range sInner := by
          rintro ⟨r, hr⟩
          have hEq : iInner (sInner r) = iComp (sComp r) :=
            (hFree.overlap (sInner r) (sComp r)).mpr
              ⟨r, rfl, rfl⟩
          have heU : iInner e ∈ U := by
            refine ⟨sComp r, ⟨r, rfl⟩, ?_⟩
            calc
              iComp (sComp r) = iInner (sInner r) := hEq.symm
              _ = iInner e := congrArg iInner hr
          exact a.2 (he ▸ heU)
        have hEdge : GaifmanAdjacent Old.graph (iInner e) c.1 := by
          rw [he]
          exact hedge
        exact fullFreeAmalgam_leftPrivate_neighbor_in_left
          hFree e hePrivate c.1 hEdge
  intro hbD
  obtain ⟨hbNotU, hbPath⟩ := hbD
  obtain ⟨e, he⟩ :=
    hStay ⟨iComp b, hbNotU⟩ hbPath
  obtain ⟨r, _, hrComp⟩ := (hFree.overlap e b).mp he
  exact hbPrivate ⟨r, hrComp.symm⟩

/-- The exact set of RIGHT-PRIVATE retained source vertices belonging
to the older outer T-component is unchanged by a literal full
functional inner-piece flip, even when the two cuts are incomparable.

Both root-attachment conditions are expressed on genuine SOURCE
vertices, not target-map images. The old single-inner-component
hypothesis will be discharged by the actual geometric chart
(#749); the new root attachment follows from a genuine new
minimal inner piece by the verified incomparable-cut lemma (#722).

The conclusion concerns only right-PRIVATE vertices; identifying
the entire new outer component and proving its full generated
boundary are separate next steps. -/
theorem fullFreeAmalgam_privateOuterComponent_iff
    {H E E' B W W' : Type v}
    {Root : Structure L H}
    {OldInner : Structure L E}
    {NewInner : Structure L E'}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sOldInner : Structure.Embedding Root OldInner}
    {sNewInner : Structure.Embedding Root NewInner}
    {sComp : Structure.Embedding Root Complement}
    {iOldInner : Structure.Embedding OldInner Old}
    {iOldComp : Structure.Embedding Complement Old}
    {iNewInner : Structure.Embedding NewInner New}
    {iNewComp : Structure.Embedding Complement New}
    (hOld : Structure.IsFreeAmalgam
      sOldInner sComp iOldInner iOldComp)
    (hNew : Structure.IsFreeAmalgam
      sNewInner sComp iNewInner iNewComp)
    (T : Set B)
    (dOld : {w : W // w ∉ iOldComp '' Set.range sComp})
    (hdOldInner : dOld.1 ∈ Set.range iOldInner)
    (hOldPrivateInD :
      ∀ e : E, e ∉ Set.range sOldInner →
        iOldInner e ∈ componentFrom Old.graph
          (iOldComp '' Set.range sComp) dOld)
    (xOld : {w : W // w ∉ iOldComp '' T})
    (hxOld :
      xOld.1 ∈ componentFrom Old.graph
        (iOldComp '' Set.range sComp) dOld)
    (xNew : {w : W' // w ∉ iNewComp '' T})
    (hxNew : xNew.1 ∈ Set.range iNewInner)
    (hRootOld :
      ∀ r : H, sComp r ∉ T →
        iOldComp (sComp r) ∈
          componentFrom Old.graph (iOldComp '' T) xOld)
    (hRootNew :
      ∀ r : H, sComp r ∉ T →
        iNewComp (sComp r) ∈
          componentFrom New.graph (iNewComp '' T) xNew)
    (b : B)
    (hbPrivate : b ∉ Set.range sComp)
    (hbNotT : b ∉ T) :
    iOldComp b ∈ componentFrom Old.graph (iOldComp '' T) xOld ↔
      iNewComp b ∈ componentFrom New.graph (iNewComp '' T) xNew := by
  constructor
  · intro hbOld
    have hOldPath : ReachOutside Old.graph (iOldComp '' T) xOld
        (fullFunctionalEmbedding_outsideCut iOldComp T
          ⟨b, hbNotT⟩) := hbOld.2
    have hNotD :
        iOldComp b ∉ componentFrom Old.graph
          (iOldComp '' Set.range sComp) dOld :=
      fullFreeAmalgam_innerComponent_avoids_rightPrivate
        hOld dOld hdOldInner b hbPrivate
    have hAttached :
        ∀ r : {v : B // v ∉ T},
          r.1 ∈ Set.range sComp →
          iNewComp r.1 ∈ componentFrom New.graph
            (iNewComp '' T) xNew := by
      intro r hr
      obtain ⟨u, hu⟩ := hr
      have huNotT : sComp u ∉ T := by
        intro huT
        exact r.2 (hu ▸ huT)
      rw [← hu]
      exact hRootNew u huNotT
    exact fullFreeAmalgam_retainedInterior_attaches_to_newOuterComponent
      hOld iNewComp T dOld hOldPrivateInD
      xOld hxOld xNew hAttached
      ⟨b, hbNotT⟩ hNotD hOldPath
  · intro hbNew
    have hNewPath : ReachOutside New.graph (iNewComp '' T) xNew
        (fullFunctionalEmbedding_outsideCut iNewComp T
          ⟨b, hbNotT⟩) := hbNew.2
    exact fullFreeAmalgam_newOuterRightPrivate_inside_oldComponent
      hNew iOldComp T xOld hRootOld
      xNew hxNew b hbPrivate hbNotT hNewPath

end AllThoseRamseyClasses.Lifts
