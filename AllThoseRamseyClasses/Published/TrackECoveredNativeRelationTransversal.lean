import AllThoseRamseyClasses.Published.TrackENativePartiteActualHSparseWitness
import PartiteConstruction.Functional.WholeMaskCoveredUnaryPart2019

/-!
# Appendix A Track E: protect native RELATION-tuple transversality

The genuine 2019 partite target has a recovered part map and function
fibre transversality, but the full native `FunctionalPartite.System`
interface also requires relation-tuple transversality. That condition
is independent of fibre transversality and cannot be assumed for
arbitrary input B.

Under the ACTUAL final protected canonical B-copy coverage, every
old primitive relation tuple in the decoded target has an ordinary
irreducible EXACT tuple support. Coverage embeds this literal support
fully into canonical B; the full OLD embedding reflects the same
original relation and the unary part label of each input vertex.
Consequently, if B's native relations are transversal, then the
decoded target's native relations are also transversal on the SAME
recovered vertex parts. No output-fibre or strict-tree assumption is
needed in this proof, and nullary relations are included.

This is separate from function-output transversality: both will be
needed if the actual final native decoder is to be packaged as
`FunctionalPartite.System`.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Native relation-tuple part transversality: distinct vertices of an
actual primitive relation tuple have DISTINCT parts, irrespective of
the set-valued functions and their domains. -/
def NativeRelationTupleTransversal {X : Type w}
    (A : Structure L X) (part : X → Parts) : Prop :=
  ∀ R xs, A.rel R xs → ∀ i j,
    part (xs i) = part (xs j) → xs i = xs j

/-- A FINAL U-closed B-covered whole-mask tagged target inherits
native relation-tuple transversality from the same canonical B.
The native target uses the literal `wholeMaskOriginalDecode C` carrier
and its ACTUAL recovered part map.

No assumption that earlier intermediate relational pictures decode to
functional targets; no change to the tested tuple's support, no
generated hull and no function-arity positivity condition. -/
theorem coveredNativeRelationTupleTransversal
    {X Y : Type w}
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X)
    (B : Structure L Y) (partB : Y → Parts)
    (hClosed : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCover : ∀ {T : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      RelStructure.Embedding Test C →
      Nonempty (RelStructure.Embedding Test
        (wholeMaskTagExpansion
          (((B.toNonemptyPartial).withParts partB).wholeMaskPatternGraph partB))))
    (hRelB : NativeRelationTupleTransversal B partB) :
    NativeRelationTupleTransversal
      (wholeMaskOriginalDecode C).collapseDomain
      (wholeMaskCoveredPart C B.toNonemptyPartial partB hClosed hCover) := by
  classical
  intro R xs hRel i j hPart
  let S : Set X := Set.range xs
  have hTagged : C.rel
      (.inl (.inl (.inl (ULift.up R)))) xs := by
    exact hRel
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inl (.inl (ULift.up R)))) xs hTagged
  obtain ⟨g⟩ := weak_irreducible_embeds_base_of_closed_coverage
    hClosed hCover S hIrred
  let xsS : Fin (L.relArity R) → S :=
    fun k => ⟨xs k, ⟨k, rfl⟩⟩
  have hRelS : (C.induce S).rel
      (.inl (.inl (.inl (ULift.up R)))) xsS := by
    exact hTagged
  have hRelBOLD :
      (wholeMaskTagExpansion
        (((B.toNonemptyPartial).withParts partB).wholeMaskPatternGraph partB)).rel
        (.inl (.inl (.inl (ULift.up R)))) (g ∘ xsS) :=
    (g.map_rel_iff
      (.inl (.inl (.inl (ULift.up R)))) xsS).mpr hRelS
  have hRelBtuple : B.rel R (g ∘ xsS) := by
    exact hRelBOLD
  let partD : X → Parts :=
    wholeMaskCoveredPart C B.toNonemptyPartial partB hClosed hCover
  have hBpart (k : Fin (L.relArity R)) :
      partB (g (xsS k)) = partD (xs k) := by
    have hPartC : WholeMaskVertexPartHolds C (xs k) (partD (xs k)) :=
      wholeMaskCoveredPart_holds
        C B.toNonemptyPartial partB hClosed hCover (xs k)
    have hPartS : (C.induce S).rel
        (.inl (.inl (.inr (partD (xs k)))))
        (fun _ : Fin 1 => xsS k) := by
      exact hPartC
    have hPartBOLD :=
      (g.map_rel_iff
        (.inl (.inl (.inr (partD (xs k)))))
        (fun _ : Fin 1 => xsS k)).mpr hPartS
    exact hPartBOLD
  have hEqualParts :
      partB (g (xsS i)) = partB (g (xsS j)) := by
    calc
      partB (g (xsS i)) = partD (xs i) := hBpart i
      _ = partD (xs j) := hPart
      _ = partB (g (xsS j)) := (hBpart j).symm
  have hImages : g (xsS i) = g (xsS j) :=
    hRelB R (g ∘ xsS) hRelBtuple i j hEqualParts
  have hPreimages : xsS i = xsS j := g.injective hImages
  exact congrArg Subtype.val hPreimages

end AllThoseRamseyClasses.Published
