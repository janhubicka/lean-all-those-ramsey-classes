import AllThoseRamseyClasses.Lifts.EHNFirstSeamAttachmentEdge
import AllThoseRamseyClasses.Lifts.EHNFiniteSeamClosureGrowth
import AllThoseRamseyClasses.Lifts.EHNTwoExteriorComponentsSelectedPiece

/-!
# Track D: constructively saturate one original seam hull into a genuine forbidden piece

This combines three separate, tightly scoped native results:

* the TRUE original source common-root preimage is function-closed;
* a left-to-right Gaifman path avoiding a closed S inside that root
  contains a first REAL left-exclusive-to-seam source attachment
  edge, whose seam endpoint is a source vertex OUTSIDE S;
* adjoining this vertex and closing under all original native
  partial/set-valued functions strictly grows S, and this process
  terminates under the finite source cardinality budget.

For a FINITE CONNECTED genuinely forbidden source mapping EHN
into a FULL native free amalgam and selected actual original
left-exclusive/right-exclusive source vertices x,y, this produces
a FINITE sequence of genuinely CLOSED source sets S0 ⊆ ... ⊆ K,
each step certified by an ACTUAL first positive Gaifman attachment
edge on a path avoiding its source, and an ACTUAL positive-width
forbidden geometric minimal closed-separator piece rooted inside K.

The full rooted pattern comes from the ACTUAL unchanged forbidden
source. It has the original native relation tables and complete
function fibres. Weak source image quotients, guessed root profiles,
and false target-root injectivity play no part.

IMPORTANT: the source root of the final selected piece can still
have COLLIDING target images; this theorem does NOT establish
the original 2019 Claim 2 selected-Q source flip or strong AP.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A single certified source-side enlargement from a left-exclusive
anchor x: the new seam generator z has an ORIGINAL positive
Gaifman attachment edge from an actual left-exclusive source
vertex a reachable from x by a path avoiding the current S.

The edge and the entire prefix path are retained, not replaced by
an arbitrary new seam vertex or by a weak quotient coordinate. -/
def NativeLeftSeamAttachmentProgress
    {V UX UA UT : Type}
    (Source : Structure L V)
    {Root : Structure L UX}
    {Left : Structure L UA}
    {Target : Structure L UT}
    (sL : Structure.Embedding Root Left)
    (jL : Structure.Embedding Left Target)
    (f : V → UT)
    (x : V)
    (S : Set V) (z : V) : Prop :=
  ∃ (a : V) (ha : a ∉ S) (hx : x ∉ S),
    a ∈ weakFreeLeftPart (sL := sL) (iL := jL) f ∧
    GaifmanAdjacent Source.graph a z ∧
    ReachOutside Source.graph S ⟨x, hx⟩ ⟨a, ha⟩

/-- The native *bounded saturation-to-selected-piece* result.

From any genuine native function-CLOSED original source set S0
inside the FULL common-root preimage, if the original finite
connected forbidden EHN witness has a left-exclusive vertex x
and a right-exclusive vertex y, there exist:

* an ACTUAL native closed set K ⊆ the common root preimage,
  reached from S0 by a finite reflexive/transitive sequence of
  witnessed FULL native closure extensions;
* each extension adjoins a FRESH original seam source vertex
  connected by a true first left-exclusive-to-seam Gaifman edge
  whose left endpoint is reached from x avoiding the prior set;
* an ACTUAL positive-width minimal-closed-separator forbidden
  geometric piece in the unchanged original forbidden source,
  with full ordered source root lying inside K, and whose two
  separated original vertices are exactly x and y.

The finite termination proof is inherited from
`finiteNativeClosedRoot_saturation` and its strict original-source
vertex budget. We do NOT assert that the output piece is the
initial defective input hull, that its target ordered roots are
injectively mapped, or that its global class can be flipped. -/
theorem finiteForbiddenEHNWitness_seamAttachmentSaturation_selectsPiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    (hFinite : Finite V)
    (hForbidden : F Source)
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (x y : V)
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := jL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := jL) (iR := jR) f)
    (S0 : Set V)
    (hS0Closed : Source.IsClosed S0)
    (hS0Root :
      S0 ⊆ weakFreeRootPart (sL := sL) (iL := jL) f) :
    ∃ K : Set V,
      Relation.ReflTransGen
        (NativeClosedRootProgress Source
          (weakFreeRootPart (sL := sL) (iL := jL) f)
          (NativeLeftSeamAttachmentProgress Source sL jL f x))
        S0 K ∧
      Source.IsClosed K ∧
      K ⊆ weakFreeRootPart (sL := sL) (iL := jL) f ∧
      ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
        0 < n ∧
        Set.range d.roots ⊆ K ∧
        d.left.1 = x ∧
        d.right.1 = y ∧
        geometricFunctionalRootedPattern Source d ∈
          forbiddenGeometricFunctionalPieces F n := by
  classical
  letI : Finite V := hFinite
  let R : Set V := weakFreeRootPart (sL := sL) (iL := jL) f
  have hRClosed : Source.IsClosed R :=
    weakFreeRootPart_isClosed (sL := sL) (iL := jL) f hf.1
  let Stop : Set V → Prop := fun S =>
    ∀ (hxS : x ∉ S) (hyS : y ∉ S),
      ¬ ReachOutside Source.graph S
        ⟨x, hxS⟩ ⟨y, hyS⟩
  let P : Set V → V → Prop :=
    NativeLeftSeamAttachmentProgress Source sL jL f x
  have hProgress :
      ∀ S : Set V, Source.IsClosed S → S ⊆ R → ¬ Stop S →
        ∃ z : V, z ∈ R ∧ z ∉ S ∧ P S z := by
    intro S _hClosed hSRoot hNotStop
    have hxS : x ∉ S := by
      intro hxs
      exact hx.2 (hSRoot hxs)
    have hyS : y ∉ S := by
      intro hys
      exact hy.2 (hSRoot hys)
    have hPath : ReachOutside Source.graph S
        ⟨x, hxS⟩ ⟨y, hyS⟩ := by
      by_contra hNoPath
      apply hNotStop
      intro hxa hya hReach
      apply hNoPath
      simpa using hReach
    obtain ⟨a, b, ha, hb, hLeftA, hRootB, hEdge, hReachA⟩ :=
      weakExclusiveGaifmanPath_has_freshLeftSeamAttachmentEdge
        Source Root Left Right Target
        sL sR jL jR hFree f hf
        S hSRoot x y hx hy hPath
    exact ⟨b, hRootB, hb, a, ha, hxS,
      hLeftA, hEdge, hReachA⟩
  obtain ⟨K, hSteps, hKClosed, hKRoot, hStop⟩ :=
    finiteNativeClosedRoot_saturation
      Source R hRClosed Stop P hProgress
      S0 hS0Closed hS0Root
  have hxK : x ∉ K := by
    intro h
    exact hx.2 (hKRoot h)
  have hyK : y ∉ K := by
    intro h
    exact hy.2 (hKRoot h)
  let xK : {v : V // v ∉ K} := ⟨x, hxK⟩
  let yK : {v : V // v ∉ K} := ⟨y, hyK⟩
  have hSeparated : ¬ ReachOutside Source.graph K xK yK :=
    hStop hxK hyK
  have hPathFull :
      Relation.ReflTransGen
        (GaifmanAdjacent Source.graph) x y :=
    (hConnected Source hFinite hForbidden).2 x y
  obtain ⟨n, d, hn, hRoot, hLeft, hRight⟩ :=
    finiteClosedCut_twoExteriorComponents_selectPositivePiece
      Source K hKClosed xK yK hSeparated hPathFull
  have hForbiddenPiece :
      geometricFunctionalRootedPattern Source d ∈
        forbiddenGeometricFunctionalPieces F n := by
    change IsForbiddenGeometricFunctionalPiece F
      (geometricFunctionalRootedPattern Source d)
    exact ⟨V, Source, inferInstance, hForbidden, d,
      ⟨RootedPatternIso.refl _⟩⟩
  exact ⟨K, hSteps, hKClosed, hKRoot, n, d, hn,
    hRoot, hLeft, hRight, hForbiddenPiece⟩

end AllThoseRamseyClasses.Lifts
