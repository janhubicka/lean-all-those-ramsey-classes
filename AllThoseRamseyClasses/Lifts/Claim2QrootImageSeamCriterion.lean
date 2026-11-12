import AllThoseRamseyClasses.Lifts.Claim2ComplementLocalSeamInj

/-!
# Exact Q-root-image seam injectivity without common-root alignment

The actual 2019 source separator Q.rootEmbedding need not be a copy of
the ENTIRE target overlap X. Thus the full-target-seam iff from the
aligned-root interface cannot be applied without extra geometric data.

This module instead uses the literal TARGET IMAGE of the actual SOURCE
Q root:
  S_Q := range (fun r => flip (iNewQ (qRoot r))).

For this explicitly smaller seam, COMPLETE new source-map injectivity
is equivalent to reflection of S_Q by the Q-side map. The reverse
direction uses only old injectivity on the retained source complement
whose images are in S_Q. No full common-root identification is assumed.

The result does not claim that S_Q is the entire target common seam,
nor that the canonical Q selection automatically supplies reflection.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Exact complement target-coordinate agreement transports OLD
complement-local seam injectivity to the NEW retained complement.
No statement about the new Q-exclusive source vertices is made. -/
theorem fullNativeReplacement_newComplement_seamInjective_of_local
    {V W E UT : Type}
    {Old : Structure L V} {New : Structure L W}
    {Complement : Structure L E}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (f : V → UT) (flip : W → UT)
    (Seam : Set UT)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩ (f ⁻¹' Seam)))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e)) :
    Set.InjOn flip (Set.range iNewE ∩ (flip ⁻¹' Seam)) := by
  intro x hx y hy hEqual
  obtain ⟨⟨e₁, he₁⟩, hxSeam⟩ := hx
  obtain ⟨⟨e₂, he₂⟩, hySeam⟩ := hy
  have hSeam₁ : flip (iNewE e₁) ∈ Seam := by
    rw [he₁]
    exact hxSeam
  have hSeam₂ : flip (iNewE e₂) ∈ Seam := by
    rw [he₂]
    exact hySeam
  have hEqualE : flip (iNewE e₁) = flip (iNewE e₂) := by
    calc
      flip (iNewE e₁) = flip x := congrArg flip he₁
      _ = flip y := hEqual
      _ = flip (iNewE e₂) := (congrArg flip he₂).symm
  have hEeq : e₁ = e₂ :=
    fullNativeReplacement_retainedComplement_seamInjective_of_local
      iOldE iNewE f flip Seam hOldLocalInj hSameComplement
      e₁ e₂ hSeam₁ hSeam₂ hEqualE
  calc
    x = iNewE e₁ := he₁.symm
    _ = iNewE e₂ := congrArg iNewE hEeq
    _ = y := he₂

/-- Injectivity of the NEW source map on the image of the ACTUAL Q
root already forces every Q vertex whose target image lies in this
root image to be a Q-root vertex.

Unlike the full target-seam criterion, this direction needs neither
any old source, nor target-side embeddings, nor free amalgamation. -/
theorem fullNativeReplacement_newQrootImageSeamInj_implies_QrootReflection
    {R Q W UT : Type}
    {Root : Structure L R}
    {Replacement : Structure L Q}
    {New : Structure L W}
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (flip : W → UT)
    (hNewInj : Set.InjOn flip
      (flip ⁻¹' Set.range
        (fun r : R => flip (iNewQ (qRoot r))))) :
    ∀ q : Q,
      flip (iNewQ q) ∈
          Set.range (fun r : R => flip (iNewQ (qRoot r))) →
        q ∈ Set.range qRoot := by
  intro q hImage
  obtain ⟨r, hr⟩ := hImage
  have hRootIn :
      flip (iNewQ (qRoot r)) ∈
        Set.range (fun r : R => flip (iNewQ (qRoot r))) :=
    ⟨r, rfl⟩
  have hSourceEq : iNewQ q = iNewQ (qRoot r) :=
    hNewInj hImage hRootIn hr.symm
  exact ⟨r, (iNewQ.injective hSourceEq).symm⟩

/-- Exact ROOT-IMAGE seam criterion, without any full identification
between the source Q-root and the possibly larger target common root.

If the OLD map is injective on the retained complement vertices whose
images fall into the TARGET IMAGE S_Q of the Q-root, then the NEW weak
map is injective on its entire preimage of S_Q iff Q reflects S_Q:
every Q vertex mapped into S_Q is already in its SOURCE root.

S_Q need NOT equal the actual full target common seam. -/
theorem fullNativeReplacement_newQrootImageSeamInj_iff_QrootReflection
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
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩
        (f ⁻¹' Set.range
          (fun r : R => flip (iNewQ (qRoot r))))))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e)) :
    Set.InjOn flip
      (flip ⁻¹' Set.range
        (fun r : R => flip (iNewQ (qRoot r)))) ↔
      ∀ q : Q,
        flip (iNewQ q) ∈
          Set.range (fun r : R => flip (iNewQ (qRoot r))) →
          q ∈ Set.range qRoot := by
  let Seam : Set UT :=
    Set.range (fun r : R => flip (iNewQ (qRoot r)))
  constructor
  · intro hNew
    exact fullNativeReplacement_newQrootImageSeamInj_implies_QrootReflection
      iNewQ qRoot flip hNew
  · intro hReflect
    exact fullNativeReplacement_newSeamInj_of_local_and_QrootReflection
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      f flip Seam hOldLocalInj hSameComplement hReflect

end AllThoseRamseyClasses.Lifts
