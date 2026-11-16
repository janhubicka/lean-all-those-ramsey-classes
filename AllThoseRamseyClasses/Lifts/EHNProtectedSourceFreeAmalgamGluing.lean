import AllThoseRamseyClasses.Lifts.EHNNativePermanentRootPaletteObstruction
import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam

/-!
# Track D: full native source-free-amalgam gluing of EHN side maps

Let an ORIGINAL source S be a genuine full NATIVE free amalgam
of two source sides P,Q over a FULL source root R. Suppose P and
Q possess weak EHN maps to ANY common target D, agreeing
pointwise on R. The side maps need NOT be globally injective;
all source root vertices may have collided images.

The maps glue to a genuine EHN S→D: positive relations and
complete set-valued native function incidences are carried by
one source side, and every irreducible FULL source test factors
FULLY through one source side. Thus arbitrary extra CROSS
target tuples do not obstruct EHN, since the relevant FULL
tests have their images entirely inside one protected side.

This is the semantic mechanism used in the 16 November
permanently incompatible rooted halves counterexample, but
does not construct that infinite coloured family. In particular
a whole source with the requisite free diagram can be
forbidden inside EVERY allowed target amalgam of two protected
halves, not merely inside the free target amalgam.

The second theorem instantiates the obstruction with the actual
native Forb_EHN(F) avoidance predicate: two target full
rooted extensions are permanently nonamalgamable if one
forbidden source has a full free diagram with genuine
EHN side maps to the target extensions whose root images
factor through their shared target root.

The construction does not assume that the source-side EHN
maps are FULL embeddings, and does not change frozen 2019 text.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A genuinely constructed ORIGINAL native EHN map into an
ARBITRARY common target, obtained by gluing compatible side
EHN maps over a complete source FREE-AMALGAM diagram.

The side maps may be noninjective and can identify distinct
source-root vertices. No strong-amalgamation or source
root-injection hypothesis is used. The conclusion retains
positive native function incidences and full irreducible-test
reflection, not just graph homomorphism. -/
theorem nativeSourceFreeAmalgam_glue_EHN_sideMaps
    {RR VL VR VS VT : Type}
    (Root : Structure L RR)
    (Left : Structure L VL)
    (Right : Structure L VR)
    (Source : Structure L VS)
    (Target : Structure L VT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (iL : Structure.Embedding Left Source)
    (iR : Structure.Embedding Right Source)
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (uL : VL → VT) (uR : VR → VT)
    (huL : Left.IsEHNHomomorphismEmbedding Target uL)
    (huR : Right.IsEHNHomomorphismEmbedding Target uR)
    (hRootAgree : ∀ r : RR, uL (sL r) = uR (sR r)) :
    ∃ f : VS → VT,
      Source.IsEHNHomomorphismEmbedding Target f ∧
      (∀ a : VL, f (iL a) = uL a) ∧
      (∀ b : VR, f (iR b) = uR b) := by
  classical
  have hRightExists (z : VS)
      (hNotLeft : ¬ ∃ a : VL, iL a = z) :
      ∃ b : VR, iR b = z :=
    (hFree.covers z).resolve_left hNotLeft
  have hImagesMatch (a : VL) (b : VR)
      (hab : iL a = iR b) : uL a = uR b := by
    obtain ⟨r, hrL, hrR⟩ := (hFree.overlap a b).mp hab
    calc
      uL a = uL (sL r) := congrArg uL hrL.symm
      _ = uR (sR r) := hRootAgree r
      _ = uR b := congrArg uR hrR
  let f : VS → VT := fun z =>
    if h : ∃ a : VL, iL a = z then
      uL (Classical.choose h)
    else
      uR (Classical.choose (hRightExists z h))
  have hOnLeft (a : VL) : f (iL a) = uL a := by
    have h : ∃ a' : VL, iL a' = iL a := ⟨a, rfl⟩
    unfold f
    rw [dif_pos h]
    exact congrArg uL
      (iL.injective (Classical.choose_spec h))
  have hOnRight (b : VR) : f (iR b) = uR b := by
    by_cases h : ∃ a : VL, iL a = iR b
    · unfold f
      rw [dif_pos h]
      exact hImagesMatch (Classical.choose h) b
        (Classical.choose_spec h)
    · unfold f
      rw [dif_neg h]
      have hChoice :
          iR (Classical.choose (hRightExists (iR b) h)) =
            iR b :=
        Classical.choose_spec (hRightExists (iR b) h)
      exact congrArg uR (iR.injective hChoice)
  have hWeak : Source.IsWeakHomomorphism Target f := by
    constructor
    · intro Rel xs hSource
      rcases (hFree.rel_iff Rel xs).mp hSource with hLeft | hRight
      · obtain ⟨ys, hYS, hXs⟩ := hLeft
        have hArgs : f ∘ xs = uL ∘ ys := by
          funext k
          calc
            f (xs k) = f (iL (ys k)) :=
              congrArg f (congrFun hXs k).symm
            _ = uL (ys k) := hOnLeft _
        rw [hArgs]
        exact huL.1.1 Rel ys hYS
      · obtain ⟨ys, hYS, hXs⟩ := hRight
        have hArgs : f ∘ xs = uR ∘ ys := by
          funext k
          calc
            f (xs k) = f (iR (ys k)) :=
              congrArg f (congrFun hXs k).symm
            _ = uR (ys k) := hOnRight _
        rw [hArgs]
        exact huR.1.1 Rel ys hYS
    · intro Fun xs out hSource
      rcases (hFree.func_iff Fun xs out).mp hSource with hLeft | hRight
      · obtain ⟨ys, z, hYZ, hXs, hOut⟩ := hLeft
        have hArgs : f ∘ xs = uL ∘ ys := by
          funext k
          calc
            f (xs k) = f (iL (ys k)) :=
              congrArg f (congrFun hXs k).symm
            _ = uL (ys k) := hOnLeft _
        have hVal : f out = uL z := by
          calc
            f out = f (iL z) := congrArg f hOut.symm
            _ = uL z := hOnLeft z
        rw [hVal, hArgs]
        exact huL.1.2 Fun ys z hYZ
      · obtain ⟨ys, z, hYZ, hXs, hOut⟩ := hRight
        have hArgs : f ∘ xs = uR ∘ ys := by
          funext k
          calc
            f (xs k) = f (iR (ys k)) :=
              congrArg f (congrFun hXs k).symm
            _ = uR (ys k) := hOnRight _
        have hVal : f out = uR z := by
          calc
            f out = f (iR z) := congrArg f hOut.symm
            _ = uR z := hOnRight z
        rw [hVal, hArgs]
        exact huR.1.2 Fun ys z hYZ
  have hEHN : Source.IsEHNHomomorphismEmbedding Target f := by
    constructor
    · exact hWeak
    · intro X E hIr e
      rcases hIr hFree e with hLeft | hRight
      · let sideMap : X → VL :=
          fun x => Classical.choose (hLeft x)
        have hFactor (x : X) : e x = iL (sideMap x) :=
          Classical.choose_spec (hLeft x)
        let eSide : Structure.Embedding E Left :=
          e.factorWithMap iL sideMap hFactor
        obtain ⟨eTarget, hTarget⟩ := huL.2 E hIr eSide
        refine ⟨eTarget, ?_⟩
        intro x
        calc
          eTarget x = uL (eSide x) := hTarget x
          _ = uL (sideMap x) := rfl
          _ = f (iL (sideMap x)) := (hOnLeft _).symm
          _ = f (e x) := congrArg f (hFactor x).symm
      · let sideMap : X → VR :=
          fun x => Classical.choose (hRight x)
        have hFactor (x : X) : e x = iR (sideMap x) :=
          Classical.choose_spec (hRight x)
        let eSide : Structure.Embedding E Right :=
          e.factorWithMap iR sideMap hFactor
        obtain ⟨eTarget, hTarget⟩ := huR.2 E hIr eSide
        refine ⟨eTarget, ?_⟩
        intro x
        calc
          eTarget x = uR (eSide x) := hTarget x
          _ = uR (sideMap x) := rfl
          _ = f (iR (sideMap x)) := (hOnRight _).symm
          _ = f (e x) := congrArg f (hFactor x).symm
  exact ⟨f, hEHN, hOnLeft, hOnRight⟩

/-- The exact ACTUAL permanent incompatibility obstruction:
an ORIGINAL forbidden source S decomposed as a complete
native free amalgam of two halves cannot have its half EHN
maps realized inside a common allowed target, even if that
target adds arbitrary cross relations, functions, vertices
or identifies other target coordinates.

The root maps from the source half roots to the OLD target
root can be NONINJECTIVE. Each half weak EHN map is separately
protected by a FULL embedding of its actual target half.

This proves NONAMALGAMABILITY, not merely failure of a free
target amalgam, directly in the semantic Forb_EHN(F) class. -/
theorem forbiddenNativeSource_freeDiagram_halfMaps_permanentlyIncompatible
    (F : ∀ {X : Type}, Structure L X → Prop)
    {RS RL RR VS VA VB VX : Type}
    (SourceRoot : Structure L RS)
    (SourceLeft : Structure L RL)
    (SourceRight : Structure L RR)
    (Forbidden : Structure L VS)
    (TargetRoot : Structure L VX)
    (TargetLeft : Structure L VA)
    (TargetRight : Structure L VB)
    (sL : Structure.Embedding SourceRoot SourceLeft)
    (sR : Structure.Embedding SourceRoot SourceRight)
    (iL : Structure.Embedding SourceLeft Forbidden)
    (iR : Structure.Embedding SourceRight Forbidden)
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (hFinite : Finite VS) (hForbidden : F Forbidden)
    (jL : Structure.Embedding TargetRoot TargetLeft)
    (jR : Structure.Embedding TargetRoot TargetRight)
    (uL : RL → VA) (uR : RR → VB)
    (huL : SourceLeft.IsEHNHomomorphismEmbedding TargetLeft uL)
    (huR : SourceRight.IsEHNHomomorphismEmbedding TargetRight uR)
    (k : RS → VX)
    (hRootLeft : ∀ r : RS, uL (sL r) = jL (k r))
    (hRootRight : ∀ r : RS, uR (sR r) = jR (k r)) :
    PermanentlyIncompatibleNativeRootExtensions
      (fun {W : Type} D => AvoidsGlobalFunctionalEHN F D)
      TargetRoot TargetLeft TargetRight jL jR := by
  intro hPossible
  obtain ⟨Z, D, hAllowedD, iTargetL, iTargetR,
    hRootCommon⟩ := hPossible
  have hLeftIntoD :
      SourceLeft.IsEHNHomomorphismEmbedding D
        (iTargetL ∘ uL) :=
    iTargetL.isEHNHomomorphismEmbedding.comp huL
  have hRightIntoD :
      SourceRight.IsEHNHomomorphismEmbedding D
        (iTargetR ∘ uR) :=
    iTargetR.isEHNHomomorphismEmbedding.comp huR
  have hAgree (r : RS) :
      (iTargetL ∘ uL) (sL r) =
      (iTargetR ∘ uR) (sR r) := by
    calc
      (iTargetL ∘ uL) (sL r) =
        iTargetL (jL (k r)) :=
          congrArg iTargetL (hRootLeft r)
      _ = iTargetR (jR (k r)) := hRootCommon (k r)
      _ = (iTargetR ∘ uR) (sR r) :=
          congrArg iTargetR (hRootRight r).symm
  obtain ⟨f, hF, _, _⟩ :=
    nativeSourceFreeAmalgam_glue_EHN_sideMaps
      SourceRoot SourceLeft SourceRight Forbidden D
      sL sR iL iR hFree
      (iTargetL ∘ uL) (iTargetR ∘ uR)
      hLeftIntoD hRightIntoD hAgree
  exact hAllowedD Forbidden hFinite hForbidden f hF

end AllThoseRamseyClasses.Lifts
