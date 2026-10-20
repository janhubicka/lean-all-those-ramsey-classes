import AllThoseRamseyClasses.Lifts.ConnectedForbiddenThreeRegions
import AllThoseRamseyClasses.Lifts.PositiveGeometricRootFromConnectedPath

/-!
# Automatic positive-width genuine forbidden piece of a weak amalgam obstruction

The previous certified initial partition produces nonempty exclusive
left and right source regions and a nonempty function-closed preimage
of the common root. This module takes a genuine forbidden weak EHN
map into a FULL native free amalgam of forbidden-free witnesses and
selects an ACTUAL minimal closed separator piece between one vertex
on each exclusive side, automatically.

The finite minimal-cut chart is a bona fide piece of a forbidden
source, not an arbitrary rooted pattern. Moreover the forbidden
source is Gaifman-connected, so the selected vertices have a path
before deleting the root. Therefore its genuinely minimal separator
has POSITIVE arity, exactly as required by the original 2019
global quotient-indexed piece-relation language.

The source root tuple is injective as an enumeration, but its
IMAGE under the original weak map need not be injective. This
certifies the existence and positive-width stages of printed Claim 1
without endorsing the invalid injectivization shortcut. The
one-sided-piece selection and complete flip remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A path in the native relationalized Gaifman graph is also a
path after deleting the EMPTY cut, on the exact surviving-vertex
subtype. This transport has no connectivity or finiteness
hypothesis beyond the single supplied path. -/
theorem gaifmanPath_to_emptyCutReach
    {V : Type} (A : Structure L V)
    {x y : V}
    (hPath : Relation.ReflTransGen
      (GaifmanAdjacent A.graph) x y) :
    ReachOutside A.graph (∅ : Set V)
      (⟨x, by simp⟩ : {z : V // z ∉ ∅})
      (⟨y, by simp⟩ : {z : V // z ∉ ∅}) := by
  let lift : V → {z : V // z ∉ (∅ : Set V)} :=
    fun a => ⟨a, by simp⟩
  have go (a b : V)
      (hab : Relation.ReflTransGen
        (GaifmanAdjacent A.graph) a b) :
      ReachOutside A.graph (∅ : Set V) (lift a) (lift b) := by
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hstep ih =>
        have hOutside :
            outsideAdjacency A.graph (∅ : Set V)
              (lift a) (lift b) := hstep
        exact ih.tail hOutside
  exact go x y hPath

/-- Every connected forbidden-source witness crossing a FULL free
amalgam of two forbidden-free native structures yields an ACTUAL
positive-width geometric forbidden piece. Its root lies in the
closed common-root PREIMAGE, and the two selected separated source
vertices lie in the opposite exclusive target regions.

No global injectivity of f, nor injectivity of its root image,
is assumed or concluded. -/
theorem globalConnectedForbiddenWitness_hasPositivePiece
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type}
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    {D : Structure L UT}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    {jA : Structure.Embedding A D}
    {jB : Structure.Embedding B D}
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (hA : AvoidsGlobalFunctionalEHN F A)
    (hB : AvoidsGlobalFunctionalEHN F B)
    {U : Type} (Source : Structure L U)
    (hFin : Finite U) (hF : F Source)
    (f : U → UT)
    (hf : Source.IsEHNHomomorphismEmbedding D f) :
    ∃ (n : ℕ) (d : GeometricFunctionalPieceData Source n),
      0 < n ∧
      Set.range d.roots ⊆
        weakFreeRootPart (sL := iA) (iL := jA) f ∧
      (∃ x : U,
        x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f ∧
          d.left.1 = x) ∧
      (∃ y : U,
        y ∈ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f ∧
          d.right.1 = y) ∧
      geometricFunctionalRootedPattern Source d ∈
        forbiddenGeometricFunctionalPieces F n := by
  letI : Finite U := hFin
  obtain ⟨_, _, hLeft, hRight, _⟩ :=
    globalForbiddenConnectedWitness_threeRegions
      F hConnected hFree hA hB Source hFin hF f hf
  obtain ⟨x, hx⟩ := hLeft
  obtain ⟨y, hy⟩ := hRight
  have hPath :
      ReachOutside Source.graph (∅ : Set U)
        (⟨x, by simp⟩ : {z : U // z ∉ ∅})
        (⟨y, by simp⟩ : {z : U // z ∉ ∅}) :=
    gaifmanPath_to_emptyCutReach Source
      ((hConnected Source hFin hF).2 x y)
  obtain ⟨n, d, hPositive, hRoots, hdLeft, hdRight, hPiece⟩ :=
    weakFreePartition_hasPositiveForbiddenGeometricPiece
      F hF hFree f hf.1 x y hx hy hPath
  exact ⟨n, d, hPositive, hRoots,
    ⟨x, hx, hdLeft⟩, ⟨y, hy, hdRight⟩, hPiece⟩

end AllThoseRamseyClasses.Lifts
