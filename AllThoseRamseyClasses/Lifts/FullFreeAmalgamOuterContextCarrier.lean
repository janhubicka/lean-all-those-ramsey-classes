import AllThoseRamseyClasses.Lifts.AllRetainedOuterComponentIff

/-!
# Exact transported context carrier from retained-component equivalence

Let New be a literal FULL native functional free amalgam of a
replacement inner piece and an unchanged complement over their whole
shared functional root U. Let T be an older (possibly incomparable)
cut inside that complement, and let old C and new C' be the selected
old/new T-components.

The contextual vertex set is the entire new inner piece, together
with those retained complement vertices which belonged to the older
root-or-component set T ∪ C in Old.

Three independent source-geometric facts imply an EXACT carrier
identity with the new older geometric piece:

1. all complement vertices outside T have the same old/new outer
   component membership (the theorem of AllRetainedOuterComponentIff);
2. each surviving common root vertex U \ T belongs to C';
3. every new inner-private vertex belongs to C'.

Then the contextual carrier is literally the transported full old
cut plus the complete new T-component:

    iNewInner[univ] ∪ iNewComp[{b | iOldComp b ∈ iOldComp[T] ∪ C}]
      = iNewComp[T] ∪ C'.

This step does NOT infer private-side connectivity from a mere
generated boundary equation. Selected-Q connectivity must be
supplied separately (#881). The equality involves full SOURCE
embeddings, never weak target-map images or path identifications
through a potentially non-injective EHN map.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Retained-component equivalence, common-root attachment, and
whole new-inner-private attachment imply the exact older
root-plus-component carrier equality after a literal full native
functional free-amalgam replacement.

The older and inner cuts need not be comparable or nested. The
three hypotheses are genuine source geometry to be discharged by
the validated nested-source and selected-Q component theorems. -/
theorem fullFreeAmalgam_nestedOuterContext_carrier_eq
    {H E B W W' : Type v}
    {Root : Structure L H}
    {NewInner : Structure L E}
    {Complement : Structure L B}
    {Old : Structure L W}
    {New : Structure L W'}
    {sNewInner : Structure.Embedding Root NewInner}
    {sComp : Structure.Embedding Root Complement}
    {iNewInner : Structure.Embedding NewInner New}
    {iOldComp : Structure.Embedding Complement Old}
    {iNewComp : Structure.Embedding Complement New}
    (hNew : Structure.IsFreeAmalgam
      sNewInner sComp iNewInner iNewComp)
    (T : Set B)
    (xOld : {w : W // w ∉ iOldComp '' T})
    (xNew : {w : W' // w ∉ iNewComp '' T})
    (hRetained : ∀ b : B, b ∉ T →
      (iOldComp b ∈
        componentFrom Old.graph (iOldComp '' T) xOld ↔
       iNewComp b ∈
        componentFrom New.graph (iNewComp '' T) xNew))
    (hRootNew : ∀ r : H, sComp r ∉ T →
      iNewComp (sComp r) ∈
        componentFrom New.graph (iNewComp '' T) xNew)
    (hAllNewPrivate : ∀ e : E,
      e ∉ Set.range sNewInner →
        iNewInner e ∈
          componentFrom New.graph (iNewComp '' T) xNew) :
    iNewInner '' (Set.univ : Set E) ∪
      iNewComp '' {b : B | iOldComp b ∈
        (iOldComp '' T) ∪
          componentFrom Old.graph (iOldComp '' T) xOld} =
    (iNewComp '' T) ∪
      componentFrom New.graph (iNewComp '' T) xNew := by
  let OldC : Set W :=
    componentFrom Old.graph (iOldComp '' T) xOld
  let NewC : Set W' :=
    componentFrom New.graph (iNewComp '' T) xNew
  change iNewInner '' (Set.univ : Set E) ∪
      iNewComp '' {b : B | iOldComp b ∈
        (iOldComp '' T) ∪ OldC} =
    (iNewComp '' T) ∪ NewC
  apply Set.Subset.antisymm
  · intro w hw
    rcases hw with ⟨e, _heUniv, rfl⟩ | ⟨b, hbS, rfl⟩
    · by_cases heRoot : e ∈ Set.range sNewInner
      · obtain ⟨r, hr⟩ := heRoot
        have hCoincide :
            iNewInner e = iNewComp (sComp r) := by
          calc
            iNewInner e = iNewInner (sNewInner r) :=
              congrArg iNewInner hr.symm
            _ = iNewComp (sComp r) :=
              (hNew.overlap (sNewInner r) (sComp r)).mpr
                ⟨r, rfl, rfl⟩
        rw [hCoincide]
        by_cases hrT : sComp r ∈ T
        · exact Or.inl ⟨sComp r, hrT, rfl⟩
        · exact Or.inr (hRootNew r hrT)
      · exact Or.inr (hAllNewPrivate e heRoot)
    · rcases hbS with hbT | hbOldC
      · obtain ⟨b', hb'T, hEq⟩ := hbT
        have hSame : b' = b := iOldComp.injective hEq
        exact Or.inl ⟨b, hSame ▸ hb'T, rfl⟩
      · have hbNotT : b ∉ T := by
          intro hbT
          exact hbOldC.1 ⟨b, hbT, rfl⟩
        exact Or.inr ((hRetained b hbNotT).mp hbOldC)
  · intro w hw
    rcases hw with ⟨b, hbT, rfl⟩ | hwNewC
    · exact Or.inr ⟨b, Or.inl ⟨b, hbT, rfl⟩, rfl⟩
    · rcases hNew.covers w with ⟨e, he⟩ | ⟨b, hb⟩
      · exact Or.inl ⟨e, Set.mem_univ _, he.symm⟩
      · rw [hb] at hwNewC
        have hbNotT : b ∉ T := by
          intro hbT
          exact hwNewC.1 ⟨b, hbT, rfl⟩
        have hbOldC : iOldComp b ∈ OldC :=
          (hRetained b hbNotT).mpr hwNewC
        exact Or.inr ⟨b, Or.inr hbOldC, hb.symm⟩

end AllThoseRamseyClasses.Lifts
