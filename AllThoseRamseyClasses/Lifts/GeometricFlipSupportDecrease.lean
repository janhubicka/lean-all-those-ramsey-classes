import AllThoseRamseyClasses.Lifts.FlipSupportStrictDecrease
import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# Strict support decrease for the ACTUAL geometric minimal-cut flip

The cardinality hypothesis in the first part of the proof of
`lem:amalgamationstr` comes directly from the geometric piece:
the selected component C lies outside the opposite closed side
V\\C, so any vertex in C mapped into A\\X is an A-only vertex
that cannot belong to the preserved complement.

Combine the verified exact functional free-amalgam source
decomposition with the general strict exclusive-support inequality.
The old and new forbidden source carriers can be different; their
target maps need only agree on the complementary side. The map on
the new piece must avoid A-only, as happens when a piece is flipped
into the B-side.

No global injectivity of either weak map is assumed. The separate
original-2019 tuple-surjective forbidden-image closure argument
still has to produce an admissible injective witness before
appealing to minimality among injective forbidden maps.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {V W Z : Type v}

/-- When a selected minimal separating component contains an
A-only vertex, moving its rooted piece entirely outside A-only
STRICTLY decreases the number of A-only SOURCE vertices in
the replacement forbidden source.

The new source comes with a genuine full functional free-amalgam
diagram, and the flip map agrees on the unchanged complement.
The theorem does not assume that the flip map is injective. -/
theorem geometricFlip_exclusiveSupport_strict_decrease
    [Fintype V] [Fintype W]
    (A : Structure L V)
    {n : ℕ} (d : GeometricFunctionalPieceData A n)
    (P' : FunctionalRootExtension
      (closedCutRoot A (Set.range d.roots) d.minimal.1))
    (New : Structure L W)
    (iP : Structure.Embedding P'.str New)
    (iT : Structure.Embedding
      (componentComplementRootExtension A (Set.range d.roots)
        d.minimal.1 d.left).str New)
    (hFree : Structure.IsFreeAmalgam
      P'.rootEmbedding
      (componentComplementRootExtension A (Set.range d.roots)
        d.minimal.1 d.left).rootEmbedding
      iP iT)
    (f : V → Z) (g : W → Z)
    (AOnly : Set Z)
    (hNewPieceAvoid : ∀ a : P'.Carrier,
      g (iP a) ∉ AOnly)
    (hComplement : ∀ b :
      (componentComplementRootExtension A
        (Set.range d.roots) d.minimal.1 d.left).Carrier,
      g (iT b) = f b.1)
    (v : V)
    (hvComponent :
      v ∈ functionalComponentFrom A (Set.range d.roots) d.left)
    (hvAOnly : f v ∈ AOnly) :
    Nat.card {w : W // g w ∈ AOnly} <
      Nat.card {x : V // f x ∈ AOnly} := by
  classical
  let R : Set V := Set.range d.roots
  let C : Set V := functionalComponentFrom A R d.left
  let T := componentComplementRootExtension A R d.minimal.1 d.left
  let iOldT := functionalComponentComplementEmbedding A R d.minimal.1 d.left
  letI : Finite (Set.compl C) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (Set.compl C) := Fintype.ofFinite (Set.compl C)
  have hOldRight :
      ∀ b : T.Carrier, f (iOldT b) = f b.1 := by
    intro b
    rfl
  have hOutside :
      ∀ b : T.Carrier, v ≠ iOldT b := by
    intro b hb
    have hv : v = b.1 := hb
    have hbC : b.1 ∈ C := hv ▸ hvComponent
    exact b.2 hbC
  exact flipExclusiveSupport_strict_decrease
    (iOldR := iOldT)
    (iNewL := iP)
    (iNewR := iT)
    (sNewL := P'.rootEmbedding)
    (sRight := T.rootEmbedding)
    hFree f g (fun b : T.Carrier => f b.1)
    hOldRight hComplement AOnly
    hNewPieceAvoid v hvAOnly hOutside

end AllThoseRamseyClasses.Lifts
