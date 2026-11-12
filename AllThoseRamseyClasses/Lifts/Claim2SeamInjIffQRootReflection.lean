import AllThoseRamseyClasses.Lifts.Claim2ComplementLocalSeamInj

/-!
# Exact seam-injectivity criterion for a root-preserving Q-side weak map

Suppose a genuine native source replacement is a FULL free amalgam
Q +_Root E. The unchanged complement E has the identical target
coordinates as in the old source, and the old map is injective only
on the OLD complement vertices mapping into the target common seam.

The replacement-side weak map gQ lands in Left, with exact root
coordinates gQ(qRoot r) = iLeft r and the target factorization
flip(iNewQ q) = jLeft(gQ q).

Then the COMPLETE NEW seam preimage is injective under flip **iff**
every Q-side source vertex mapped to Left's original common root
is itself a literal Q-root vertex. This is Q root reflection.
It is a criterion, NOT a proof that canonical selected Q has it.

No target image quotient, support minimizer, source finiteness,
additional forbidden closure axiom or change to frozen 2019 TeX.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- On an actual Q +_Root E native source replacement, OLD
complement-local seam injection and the EXACT Q root coordinates
make root reflection of gQ equivalent to full injectivity of
the new weak map on the ENTIRE new common-seam preimage.

The forward direction is independent of the old-source injection;
the reverse direction uses its minimal complement-local form.
No weak homomorphism-embedding is asserted to satisfy root reflection
automatically. -/
theorem fullNativeReplacement_newSeamInj_iff_QrootReflection_of_local
    {R E Q V W UA UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    {Left : Structure L UA} {Target : Structure L UT}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (iLeft : Structure.Embedding Root Left)
    (jLeft : Structure.Embedding Left Target)
    (f : V → UT) (flip : W → UT)
    (gQ : Q → UA)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩
        (f ⁻¹' Set.range (jLeft.comp iLeft))))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hFlipQ : ∀ q : Q,
      flip (iNewQ q) = jLeft (gQ q))
    (hQRootCoords : ∀ r : R,
      gQ (qRoot r) = iLeft r) :
    Set.InjOn flip (flip ⁻¹' Set.range (jLeft.comp iLeft)) ↔
      ∀ q : Q, gQ q ∈ Set.range iLeft →
        q ∈ Set.range qRoot := by
  let Seam : Set UT := Set.range (jLeft.comp iLeft)
  constructor
  · intro hNewSeamInj q hImage
    obtain ⟨r, hr⟩ := hImage
    have hQSeam : flip (iNewQ q) ∈ Seam := by
      refine ⟨r, ?_⟩
      change jLeft (iLeft r) = flip (iNewQ q)
      calc
        jLeft (iLeft r) = jLeft (gQ q) := congrArg jLeft hr
        _ = flip (iNewQ q) := (hFlipQ q).symm
    have hSameQ : gQ q = gQ (qRoot r) :=
      hr.symm.trans (hQRootCoords r).symm
    have hSameImage :
        flip (iNewQ q) = flip (iNewQ (qRoot r)) := by
      calc
        flip (iNewQ q) = jLeft (gQ q) := hFlipQ q
        _ = jLeft (gQ (qRoot r)) := congrArg jLeft hSameQ
        _ = flip (iNewQ (qRoot r)) := (hFlipQ (qRoot r)).symm
    have hRootSeam : flip (iNewQ (qRoot r)) ∈ Seam :=
      hSameImage ▸ hQSeam
    have hSourceEq : iNewQ q = iNewQ (qRoot r) :=
      hNewSeamInj hQSeam hRootSeam hSameImage
    exact ⟨r, (iNewQ.injective hSourceEq).symm⟩
  · intro hReflect
    have hQReflectSeam : ∀ q : Q,
        flip (iNewQ q) ∈ Seam → q ∈ Set.range qRoot := by
      intro q hq
      obtain ⟨r, hr⟩ := hq
      have hImage : gQ q = iLeft r := by
        apply jLeft.injective
        calc
          jLeft (gQ q) = flip (iNewQ q) := (hFlipQ q).symm
          _ = jLeft (iLeft r) := hr.symm
      exact hReflect q ⟨r, hImage.symm⟩
    exact fullNativeReplacement_newSeamInj_of_local_and_QrootReflection
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      f flip Seam hOldLocalInj hSameComplement hQReflectSeam

/-- If the new map has a seam collision, an actual Q nonroot
vertex maps into the original target Left root. This version
requires only OLD complement-local seam injectivity, and is
obtained from the iff without a second collision proof.

It is a NECESSARY obstruction certificate; root-reflection
failure is NOT proved impossible for a canonical selected Q. -/
theorem fullNativeReplacement_collision_forces_QrootReflectionFailure_of_local
    {R E Q V W UA UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {Old : Structure L V} {New : Structure L W}
    {Left : Structure L UA} {Target : Structure L UT}
    (iOldE : Structure.Embedding Complement Old)
    (iNewE : Structure.Embedding Complement New)
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (eRoot : Structure.Embedding Root Complement)
    (hNewFree : Structure.IsFreeAmalgam qRoot eRoot iNewQ iNewE)
    (iLeft : Structure.Embedding Root Left)
    (jLeft : Structure.Embedding Left Target)
    (f : V → UT) (flip : W → UT)
    (gQ : Q → UA)
    (hOldLocalInj : Set.InjOn f
      (Set.range iOldE ∩
        (f ⁻¹' Set.range (jLeft.comp iLeft))))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hFlipQ : ∀ q : Q,
      flip (iNewQ q) = jLeft (gQ q))
    (hQRootCoords : ∀ r : R,
      gQ (qRoot r) = iLeft r)
    (hNewCollision : ¬ Set.InjOn flip
      (flip ⁻¹' Set.range (jLeft.comp iLeft))) :
    ∃ q : Q,
      q ∉ Set.range qRoot ∧
      gQ q ∈ Set.range iLeft := by
  classical
  by_contra hNoDefect
  have hReflect : ∀ q : Q,
      gQ q ∈ Set.range iLeft → q ∈ Set.range qRoot := by
    intro q hImage
    by_contra hNotRoot
    exact hNoDefect ⟨q, hNotRoot, hImage⟩
  exact hNewCollision
    ((fullNativeReplacement_newSeamInj_iff_QrootReflection_of_local
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      iLeft jLeft f flip gQ hOldLocalInj hSameComplement
      hFlipQ hQRootCoords).mpr hReflect)

end AllThoseRamseyClasses.Lifts
