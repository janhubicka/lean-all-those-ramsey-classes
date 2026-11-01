import AllThoseRamseyClasses.Lifts.NamedNestedFunctionalContext
import AllThoseRamseyClasses.Lifts.FreeAmalgamSideIso

/-!
# Recover the actual inner stage from an outer native free-amalgam test

Let Ext = T +_R Test be a full native functional extension of T.
Suppose Whole = M +_S Ext is another full native functional amalgam,
where the embedded inner root S lies inside the T-side of Ext.
The closed induced source subset

  K = iM(M) union iExt(jT(T))

is then a genuine FULL amalgam M +_S T, with side embeddings
on the original M and T carriers and exact original vertex maps.

This is a necessary diagram-construction step for Section 3 Claim 2:
the old and new pieces can both be attached to the SAME outer test
without confusing the full induced complement with a weak source
image or an anonymous graph-only union.

No nesting between the inner root S and the outer root R is assumed.
No forbidden-family membership or incompatibility conclusion is
assumed. This lemma alone does not produce a full outer-source
profile congruence, nor the missing geometric opposite boundary.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- The full native inner source stage can be recovered inside an
actual `M +_S Ext` when `T` is embedded FULLY in `Ext` and
the common root maps through `T`.  The chosen vertex set is
exactly `M ∪ T`; all relation and function fibres are reflected. -/
theorem fullFunctionalFreeAmalgam_induce_innerStage
    {S M T E X : Type v}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Ext : Structure L E} {Out : Structure L X}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {jT : Structure.Embedding Tstr Ext}
    {iM : Structure.Embedding Mstr Out}
    {iExt : Structure.Embedding Ext Out}
    (hWhole : Structure.IsFreeAmalgam
      sM (jT.comp sT) iM iExt) :
    let K : Set X :=
      iM '' (Set.univ : Set M) ∪ iExt '' (Set.range jT)
    ∃ (hK : Out.IsClosed K)
      (kM : Structure.Embedding Mstr (Out.induce K hK))
      (kT : Structure.Embedding Tstr (Out.induce K hK)),
      Structure.IsFreeAmalgam sM sT kM kT ∧
      (∀ m : M, (kM m).1 = iM m) ∧
      (∀ t : T, (kT t).1 = iExt (jT t)) := by
  classical
  let SR : Set E := Set.range jT
  have hUniv : Tstr.IsClosed (Set.univ : Set T) := by
    intro F args hargs z hz
    exact Set.mem_univ _
  have hSR : Ext.IsClosed SR := by
    simpa only [Set.image_univ] using
      (functionalEmbedding_image_closed Tstr Ext jT
        (Set.univ : Set T) hUniv)
  have hRootInSR : ∀ s : S, (jT.comp sT) s ∈ SR := by
    intro s
    exact ⟨sT s, rfl⟩
  obtain ⟨hK, sRsmall, kM, kR, hSmall, hMval, hRval, hSval⟩ :=
    fullFreeAmalgam_nestedContext_namedFullDiagram
      hWhole SR hSR hRootInSR
  let incR : Structure.Embedding (Ext.induce SR hSR) Ext :=
    Structure.inclusion Ext SR hSR
  have hRange : ∀ t : T, ∃ z : SR, jT t = incR z := by
    intro t
    exact ⟨⟨jT t, ⟨t, rfl⟩⟩, rfl⟩
  let jSmall : Structure.Embedding Tstr (Ext.induce SR hSR) :=
    jT.factorThroughClosedRange incR hRange
  have hSmallVal (t : T) : (jSmall t).1 = jT t :=
    Structure.Embedding.factorThroughClosedRange_spec
      jT incR hRange t
  have hSmallSurj : Function.Surjective jSmall := by
    intro z
    obtain ⟨t, ht⟩ := z.2
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact (hSmallVal t).trans ht
  have hRoot : ∀ s : S, jSmall (sT s) = sRsmall s := by
    intro s
    apply Subtype.ext
    calc
      (jSmall (sT s)).1 = jT (sT s) := hSmallVal (sT s)
      _ = (sRsmall s).1 := (hSval s).symm
  have hSwap :
      Structure.IsFreeAmalgam sT sM
        (kR.comp jSmall) kM :=
    freeAmalgam_precompose_left_iso
      hSmall.swap jSmall hSmallSurj sT hRoot
  refine ⟨hK, kM, kR.comp jSmall, hSwap.swap, hMval, ?_⟩
  intro t
  calc
    ((kR.comp jSmall) t).1 = (kR (jSmall t)).1 := rfl
    _ = iExt (jSmall t).1 := hRval (jSmall t)
    _ = iExt (jT t) := congrArg iExt (hSmallVal t)

end AllThoseRamseyClasses.Lifts
