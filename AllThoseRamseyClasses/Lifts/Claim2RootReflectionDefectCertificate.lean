import AllThoseRamseyClasses.Lifts.Claim2SeamCollisionNewSideLocalization

/-!
# An actual new seam collision witnesses failure of Q root reflection

Suppose a genuine full-native replacement of a finite or infinite
source replaces one complete rooted piece by a new rooted structure
Q, retaining the old native complement E. The new map agrees with
the old on E and factors through the LEFT witness on Q:
  flip ∘ iQ = jLeft ∘ gQ.

Assume the old weak map was injective on the entire preimage of
the common target root. Then a new collision in that root
necessarily involves one Q-only source vertex by the native
collision-localization theorem. Such a vertex is NOT in Q's own
root (otherwise it would also belong to the E image), but its
piece-level weak target image gQ IS in the full Left root:
  q ∉ range(Q.rootEmbedding)
  gQ q ∈ range(iLeft).

This is a specific root-reflection defect of the NEW Q-side
weak piece map. No source support minimizer, globally injective
weak map, quotient, or distinct-target-image cardinality is used.

The theorem does not rule out such defects. It identifies the
necessary missing Q-side property for seam-injectivity iteration.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A new common-seam collision, following a genuinely old-seam-
injective native free-amalgam replacement, forces an actual
nonroot vertex q of Q whose weak map gQ enters the common root
of Left. All witnesses are literal source vertices. -/
theorem fullNativeReplacement_seamCollision_forces_QrootReflectionDefect
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
    (hOldSeamInj :
      Set.InjOn f (f ⁻¹' Set.range (jLeft.comp iLeft)))
    (hSameComplement : ∀ e : E,
      flip (iNewE e) = f (iOldE e))
    (hFlipQ : ∀ q : Q,
      flip (iNewQ q) = jLeft (gQ q))
    (x y : W)
    (hxSeam : flip x ∈ Set.range (jLeft.comp iLeft))
    (hySeam : flip y ∈ Set.range (jLeft.comp iLeft))
    (hEqual : flip x = flip y)
    (hDistinct : x ≠ y) :
    ∃ q : Q,
      q ∉ Set.range qRoot ∧
      gQ q ∈ Set.range iLeft := by
  classical
  let Seam : Set UT := Set.range (jLeft.comp iLeft)
  have hDefect : ∀ q : Q,
      iNewQ q ∉ Set.range iNewE →
      flip (iNewQ q) ∈ Seam →
      q ∉ Set.range qRoot ∧ gQ q ∈ Set.range iLeft := by
    intro q hNewOnly hInSeam
    have hNotRoot : q ∉ Set.range qRoot := by
      rintro ⟨r, hr⟩
      have hOverlap : iNewQ (qRoot r) = iNewE (eRoot r) :=
        (hNewFree.overlap (qRoot r) (eRoot r)).mpr
          ⟨r, rfl, rfl⟩
      apply hNewOnly
      refine ⟨eRoot r, ?_⟩
      calc
        iNewE (eRoot r) = iNewQ (qRoot r) := hOverlap.symm
        _ = iNewQ q := congrArg iNewQ hr
    have hLeftRoot : gQ q ∈ Set.range iLeft := by
      obtain ⟨r, hr⟩ := hInSeam
      have hAtRoot : jLeft (iLeft r) = flip (iNewQ q) := by
        change jLeft (iLeft r) = flip (iNewQ q) at hr
        exact hr
      refine ⟨r, ?_⟩
      apply jLeft.injective
      calc
        jLeft (iLeft r) = flip (iNewQ q) := hAtRoot
        _ = jLeft (gQ q) := hFlipQ q
    exact ⟨hNotRoot, hLeftRoot⟩
  rcases fullNativeReplacement_newSeamCollision_hits_replacementOutsideComplement
      iOldE iNewE iNewQ qRoot eRoot hNewFree
      f flip Seam hOldSeamInj hSameComplement
      x y hxSeam hySeam hEqual hDistinct with
    ⟨⟨q, hq⟩, hNewOnly⟩ | ⟨⟨q, hq⟩, hNewOnly⟩
  · have hNewOnlyQ : iNewQ q ∉ Set.range iNewE := by
      simpa only [hq] using hNewOnly
    refine ⟨q, hDefect q hNewOnlyQ ?_⟩
    simpa only [hq] using hxSeam
  · have hNewOnlyQ : iNewQ q ∉ Set.range iNewE := by
      simpa only [hq] using hNewOnly
    refine ⟨q, hDefect q hNewOnlyQ ?_⟩
    simpa only [hq] using hySeam

end AllThoseRamseyClasses.Lifts
