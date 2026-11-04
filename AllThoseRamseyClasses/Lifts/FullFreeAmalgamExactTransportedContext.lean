import AllThoseRamseyClasses.Lifts.FullFreeAmalgamNewOuterConfinement

/-!
# Exact transported outer context is one new component plus its root

The 2019 nested source flip needs more than function-closedness of the
transported outer context.  It needs LITERAL EQUALITY between:

  (all inserted Q vertices) ∪
    (unchanged complement vertices belonging to the old outer piece)

and the full old outer root together with exactly ONE component
of the NEW source outside that root.

This lemma isolates the genuinely sufficient native geometric facts.
It is deliberately independent of finite forbidden families and
canonical lift symbols.  Let `T` be the old outer cut inside the
unchanged full complement, and let OldC and NewC be the corresponding
actual source components after deleting its old/new full images.

Assume only:
* for every surviving complement vertex outside T, old/new component
  membership is equivalent (the proved Track A private/root transport);
* every newly inserted vertex PRIVATE to its inner gluing root belongs
  to NewC (actual selected connected replacement Q);
* every common inner-root vertex surviving outside T belongs to NewC.

Then the entire new transported context is EXACTLY the old
transported root plus NewC. Both inclusions are proved using the
native full-free-amalgam coverage and complete overlap criterion,
without a weak target map, graph-induced reflection or an assumed
new-context equality.

This is a geometric carrier identity. It does not prove the
neighbourhood-generated boundary of NewC, minimality of the cut,
or an unrestricted Claim 2. Those are independent Track A inputs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Equality of the transported closed context with ONE new
outside-old-root source component plus the entire transported cut.

The unchanged old complement is fully embedded in Old, and the new
source is an ACTUAL full functional amalgam of a selected inner
replacement and that same complement. Exact source carrier coverage
and overlap, not arbitrary graph connectivity, handle the two sides.

Neither root-cut nesting nor source-to-target weak-map injectivity is
assumed. There is no forbidden-family isomorphism-closure hypothesis. -/
theorem fullFreeAmalgam_transportedContext_eq_root_union_component
    {H E B W W' : Type v}
    {InnerRoot : Structure L H}
    {NewInner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sInner : Structure.Embedding InnerRoot NewInner}
    {sComp : Structure.Embedding InnerRoot Complement}
    {iInner : Structure.Embedding NewInner New}
    {iNewComp : Structure.Embedding Complement New}
    (hNew : Structure.IsFreeAmalgam
      sInner sComp iInner iNewComp)
    (iOldComp : Structure.Embedding Complement Old)
    (T : Set B)
    (xOld : {w : W // w ∉ iOldComp '' T})
    (xNew : {w : W' // w ∉ iNewComp '' T})
    (hRetained : ∀ b : B, b ∉ T →
      (iOldComp b ∈ componentFrom Old.graph
        (iOldComp '' T) xOld ↔
       iNewComp b ∈ componentFrom New.graph
        (iNewComp '' T) xNew))
    (hNewPrivate : ∀ e : E, e ∉ Set.range sInner →
      iInner e ∈ componentFrom New.graph
        (iNewComp '' T) xNew)
    (hSharedRootAttached : ∀ r : H, sComp r ∉ T →
      iNewComp (sComp r) ∈ componentFrom New.graph
        (iNewComp '' T) xNew) :
    iInner '' (Set.univ : Set E) ∪
      iNewComp '' (iOldComp ⁻¹'
        (iOldComp '' T ∪
          componentFrom Old.graph (iOldComp '' T) xOld)) =
    iNewComp '' T ∪
      componentFrom New.graph (iNewComp '' T) xNew := by
  classical
  let OldC : Set W :=
    componentFrom Old.graph (iOldComp '' T) xOld
  let NewC : Set W' :=
    componentFrom New.graph (iNewComp '' T) xNew
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with hzInner | hzComp
    · obtain ⟨e, _he, hez⟩ := hzInner
      have heIn : iInner e ∈ iNewComp '' T ∪ NewC := by
        by_cases heRoot : e ∈ Set.range sInner
        · obtain ⟨r, hr⟩ := heRoot
          have hEq : iInner (sInner r) = iNewComp (sComp r) :=
            (hNew.overlap (sInner r) (sComp r)).mpr
              ⟨r, rfl, rfl⟩
          have heEq : iInner e = iNewComp (sComp r) := by
            rw [← hr]
            exact hEq
          rw [heEq]
          by_cases hrT : sComp r ∈ T
          · exact Or.inl ⟨sComp r, hrT, rfl⟩
          · exact Or.inr (hSharedRootAttached r hrT)
        · exact Or.inr (hNewPrivate e heRoot)
      exact hez ▸ heIn
    · obtain ⟨b, hb, hbz⟩ := hzComp
      by_cases hbT : b ∈ T
      · exact Or.inl ⟨b, hbT, hbz⟩
      · have hbOld : iOldComp b ∈ OldC := by
          rcases hb with hbOldT | hbOldC
          · obtain ⟨b', hb'T, hb'Eq⟩ := hbOldT
            have hbb : b' = b := iOldComp.injective hb'Eq
            exact False.elim (hbT (hbb ▸ hb'T))
          · exact hbOldC
        have hbNew : iNewComp b ∈ NewC :=
          (hRetained b hbT).mp hbOld
        exact Or.inr (hbz ▸ hbNew)
  · intro z hz
    rcases hz with hzT | hzNew
    · obtain ⟨b, hbT, hbz⟩ := hzT
      exact Or.inr ⟨b, Or.inl ⟨b, hbT, rfl⟩, hbz⟩
    · rcases hNew.covers z with ⟨e, hez⟩ | ⟨b, hbz⟩
      · exact Or.inl ⟨e, Set.mem_univ _, hez.symm⟩
      · have hbNew : iNewComp b ∈ NewC := by
          rw [← hbz] at hzNew
          exact hzNew
        have hbNotT : b ∉ T := by
          intro hbT
          have hzCut : z ∈ iNewComp '' T :=
            ⟨b, hbT, hbz.symm⟩
          exact hzNew.1 hzCut
        have hbOld : iOldComp b ∈ OldC :=
          (hRetained b hbNotT).mpr hbNew
        exact Or.inr ⟨b, Or.inr hbOld, hbz.symm⟩

end AllThoseRamseyClasses.Lifts
