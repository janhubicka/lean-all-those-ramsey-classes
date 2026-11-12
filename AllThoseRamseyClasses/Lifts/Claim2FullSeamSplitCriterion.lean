import AllThoseRamseyClasses.Lifts.Claim2QrootImageSeamCriterion

/-!
# Complete target-seam injection splits into two independent obstructions

For a genuine FULL native source replacement New = Q +_Root E,
the source Q root has a literal target image
  S_Q := range (fun r => flip (iNewQ (qRoot r))).

Provided S_Q is contained in the TARGET common seam X, the exact
criterion for injectivity of flip on the full new preimage of X
splits into:
* Q-root reflection relative to the smaller source-root image S_Q;
* injectivity of flip on the residual TARGET seam X \ S_Q.

This is an exact iff under old retained-complement injectivity
only on S_Q. Neither property is inferred for the canonical selected-Q
weak replacement; both remain genuine mathematical gates.
It does NOT identify source and target common-root structures.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A precise decomposition of the full target-seam collision problem
WITHOUT assuming that the source Q-root covers the entire target
common seam.

Old f need only be injective on the unchanged full complement vertices
mapping into the image of the actual source Q-root. Under that
hypothesis, the NEW map is injective on the ENTIRE target seam iff:
(1) every Q vertex mapping into the SOURCE-root image S_Q is a
    literal root vertex; and
(2) no new seam collisions occur at target points outside S_Q.

This theorem is an iff, not an existence or root-reflection proof. -/
theorem fullNativeReplacement_fullSeamInj_iff_QrootReflection_and_residualInj
    {R E Q V W UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (f : V → UT) (flip : W → UT)
    (Seam : Set UT)
    (hQrootInsideSeam : ∀ r : R,
      flip (iNewQ (qRoot r)) ∈ Seam)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩
        (f ⁻¹' Set.range
          (fun r : R => flip (iNewQ (qRoot r))))))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e)) :
    Set.InjOn flip (flip ⁻¹' Seam) ↔
      (∀ q : Q,
        flip (iNewQ q) ∈
          Set.range (fun r : R => flip (iNewQ (qRoot r))) →
        q ∈ Set.range qRoot) ∧
      Set.InjOn flip
        (flip ⁻¹' (Seam \
          Set.range (fun r : R => flip (iNewQ (qRoot r))))) := by
  let S_Q : Set UT :=
    Set.range (fun r : R => flip (iNewQ (qRoot r)))
  have hSubset : S_Q ⊆ Seam := by
    intro z hz
    obtain ⟨r, hr⟩ := hz
    exact hr ▸ hQrootInsideSeam r
  have hRootImageIff :
      Set.InjOn flip (flip ⁻¹' S_Q) ↔
        ∀ q : Q, flip (iNewQ q) ∈ S_Q →
          q ∈ Set.range qRoot :=
    fullNativeReplacement_newQrootImageSeamInj_iff_QrootReflection
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      f flip hOldLocalInj hSameComplement
  constructor
  · intro hFull
    have hRootImageInj : Set.InjOn flip (flip ⁻¹' S_Q) := by
      intro x hx y hy hEq
      exact hFull (hSubset hx) (hSubset hy) hEq
    have hResidualInj :
        Set.InjOn flip (flip ⁻¹' (Seam \ S_Q)) := by
      intro x hx y hy hEq
      exact hFull hx.1 hy.1 hEq
    exact ⟨hRootImageIff.mp hRootImageInj, hResidualInj⟩
  · rintro ⟨hReflect, hResidualInj⟩
    have hRootImageInj : Set.InjOn flip (flip ⁻¹' S_Q) :=
      hRootImageIff.mpr hReflect
    intro x hx y hy hEq
    by_cases hxRoot : flip x ∈ S_Q
    · have hyRoot : flip y ∈ S_Q := by
        rw [← hEq]
        exact hxRoot
      exact hRootImageInj hxRoot hyRoot hEq
    · have hyNotRoot : flip y ∉ S_Q := by
        intro hyRoot
        apply hxRoot
        rw [hEq]
        exact hyRoot
      exact hResidualInj ⟨hx, hxRoot⟩ ⟨hy, hyNotRoot⟩ hEq

end AllThoseRamseyClasses.Lifts
