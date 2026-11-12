import AllThoseRamseyClasses.Lifts.Claim2SeamInjectivityCriterion

/-!
# Exact replacement-side criterion for preservation of full-seam injectivity

The checked source-flip theorem retains a genuine full native
complement E and glues in one genuine rooted replacement Q.
Its selected piece-level weak map `gQ : Q → Left` maps each
Q-root coordinate r to the corresponding Left root coordinate
`iLeft r`. The full target map agrees with the old map on E
and factors through `jLeft ∘ gQ` on Q.

Given injectivity of the old weak source map on the COMPLETE
preimage of the common target seam, the NEW map is injective on
its complete seam preimage IF AND ONLY IF the Q-piece map
REFLECTS the full common root:

  ∀ q : Q, gQ q ∈ range(iLeft) → q ∈ range(qRoot).

Forward: if a Q-nonroot maps into the Left root, it collides with
the Q-root vertex carrying those same target coordinates.
Backward: root reflection excludes Q-only seam-valued source
vertices; the verified old-complement collision-localization and
no-fresh-seam lemmas then preserve full new seam injection.

This precisely isolates the missing Q-side invariant. It is NOT
claimed that a selected canonical Q automatically has root reflection.
No target-image quotient, source-cardinality identification, or
original A-support minimizing witness is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- If the new weak target map is injective over the full common
seam and a Q-root has exactly its prescribed Left-root image,
then the Q-piece map cannot send a Q-nonroot into the Left root.
No old-map property is required for this direction. -/
theorem fullNativeReplacement_seamInjective_implies_QrootReflection
    {R E Q W UA UT : Type}
    {Root : Structure L R}
    {Complement : Structure L E}
    {Replacement : Structure L Q}
    {New : Structure L W}
    {Left : Structure L UA} {Target : Structure L UT}
    (iNewQ : Structure.Embedding Replacement New)
    (qRoot : Structure.Embedding Root Replacement)
    (iLeft : Structure.Embedding Root Left)
    (jLeft : Structure.Embedding Left Target)
    (flip : W → UT)
    (gQ : Q → UA)
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hRootCoordinates : ∀ r : R, gQ (qRoot r) = iLeft r)
    (hNewInj : Set.InjOn flip
      (flip ⁻¹' Set.range (jLeft.comp iLeft))) :
    ∀ q : Q, gQ q ∈ Set.range iLeft → q ∈ Set.range qRoot := by
  intro q hAtRoot
  obtain ⟨r, hr⟩ := hAtRoot
  have hTargetSame : flip (iNewQ q) =
      flip (iNewQ (qRoot r)) := by
    calc
      flip (iNewQ q) = jLeft (gQ q) := hFlipQ q
      _ = jLeft (iLeft r) := (congrArg jLeft hr).symm
      _ = jLeft (gQ (qRoot r)) :=
        (congrArg jLeft (hRootCoordinates r)).symm
      _ = flip (iNewQ (qRoot r)) := (hFlipQ (qRoot r)).symm
  have hQseam : iNewQ q ∈
      flip ⁻¹' Set.range (jLeft.comp iLeft) := by
    change flip (iNewQ q) ∈ Set.range (jLeft.comp iLeft)
    refine ⟨r, ?_⟩
    change jLeft (iLeft r) = flip (iNewQ q)
    rw [hFlipQ q, hr]
  have hRootSeam : iNewQ (qRoot r) ∈
      flip ⁻¹' Set.range (jLeft.comp iLeft) := by
    change flip (iNewQ (qRoot r)) ∈
      Set.range (jLeft.comp iLeft)
    refine ⟨r, ?_⟩
    change jLeft (iLeft r) = flip (iNewQ (qRoot r))
    rw [hFlipQ (qRoot r), hRootCoordinates r]
  have heq : q = qRoot r :=
    iNewQ.injective (hNewInj hQseam hRootSeam hTargetSame)
  exact ⟨r, heq.symm⟩

/-- Under an old-seam-injective full native replacement, the
ROOT-REFLECTION property of the Q-piece map is sufficient for
injectivity of the entire new common-seam preimage. No assumption
that the new weak map is globally injective is used. -/
theorem fullNativeReplacement_QrootReflection_implies_seamInjective
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
    (hOldInj : Set.InjOn f
      (f ⁻¹' Set.range (jLeft.comp iLeft)))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hRootReflection :
      ∀ q : Q, gQ q ∈ Set.range iLeft → q ∈ Set.range qRoot) :
    Set.InjOn flip (flip ⁻¹' Set.range (jLeft.comp iLeft)) := by
  let Seam : Set UT := Set.range (jLeft.comp iLeft)
  have hNoFreshSeam : ∀ q : Q,
      iNewQ q ∉ Set.range iNewE →
      flip (iNewQ q) ∉ Seam := by
    intro q hFresh hSeam
    have hPieceRoot : gQ q ∈ Set.range iLeft := by
      obtain ⟨r, hr⟩ := hSeam
      change jLeft (iLeft r) = flip (iNewQ q) at hr
      have hRootImage : jLeft (iLeft r) = jLeft (gQ q) :=
        hr.trans (hFlipQ q)
      exact ⟨r, jLeft.injective hRootImage⟩
    obtain ⟨r, hr⟩ := hRootReflection q hPieceRoot
    have hCoincide : iNewQ (qRoot r) = iNewE (eRoot r) :=
      (hNewFree.overlap (qRoot r) (eRoot r)).mpr
        ⟨r, rfl, rfl⟩
    apply hFresh
    refine ⟨eRoot r, ?_⟩
    calc
      iNewE (eRoot r) = iNewQ (qRoot r) := hCoincide.symm
      _ = iNewQ q := congrArg iNewQ hr
  exact fullNativeReplacement_seamInjective_of_noFreshSeam
    iOldE iNewE iNewQ qRoot eRoot hNewFree
    f flip Seam hOldInj hSameComplement hNoFreshSeam

/-- For a real full-native Q+E source replacement whose Q-root
coordinates are preserved, old full-seam injectivity makes
new full-seam injectivity EQUIVALENT to exact Q root reflection.
This is a criterion, not a proof that selected-Q maps satisfy it. -/
theorem fullNativeReplacement_seamInjective_iff_QrootReflection
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
    (hOldInj : Set.InjOn f
      (f ⁻¹' Set.range (jLeft.comp iLeft)))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hFlipQ : ∀ q : Q, flip (iNewQ q) = jLeft (gQ q))
    (hRootCoordinates : ∀ r : R, gQ (qRoot r) = iLeft r) :
    Set.InjOn flip (flip ⁻¹' Set.range (jLeft.comp iLeft)) ↔
      (∀ q : Q,
        gQ q ∈ Set.range iLeft → q ∈ Set.range qRoot) := by
  constructor
  · intro hNew
    exact fullNativeReplacement_seamInjective_implies_QrootReflection
      iNewQ qRoot iLeft jLeft flip gQ
      hFlipQ hRootCoordinates hNew
  · intro hReflect
    exact fullNativeReplacement_QrootReflection_implies_seamInjective
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      iLeft jLeft f flip gQ hOldInj
      hSameComplement hFlipQ hReflect

end AllThoseRamseyClasses.Lifts
