import AllThoseRamseyClasses.Published.MinimalTransverseTwoSideParts2019
import PartiteConstruction.Iterated.AttachmentProjection
import PartiteConstruction.Partite.Induced

/-!
# Native 2019 transverse Hales--Jewett coordinate maps are ORDINARY HEs

The previous CI-green PRs #125 and #128 construct corrected protected
coordinate/identity retractions of actual native selected attachments
into the Old picture. The maximal weak rank gluing theorem in PR #130,
however, asks for ORDINARY relational homomorphism-embeddings on
each selected side.

A key general factor lemma proves that if A->B and B->C are positive
relational maps and the composite A->C is an ORDINARY
homomorphism-embedding, then the first factor A->B is already an
ordinary homomorphism-embedding: use induced-reflection on irreducible
tests of the composite, plus positivity of B->C.

In the actual native power, each coordinate map is positive and
the composite with the selected part projection to A is the FULL
ordinary homomorphism-embedding supplied by power_isPartiteOver.
Consequently coordinate evaluation into Old is ORDINARY HE.
The fold of this core map and the identity embeddings of attached
old copies remains ORDINARY HE on the ENTIRE selected attachment.

For a minimal transverse line family T and each exceptional line i,
the REST and SINGLE LINE have two actual ordinary side maps into Old
at their own parameter coordinates, and the maps agree in outer
part labels on the common power core. No U-closedness of the
temporary attachment or source root is assumed for these ordinary
maps; separate corrected protection is already proved under
the closedness hypotheses.

The source free cut and ROOT FACTORIZATION through two embeddings
of a fixed closed A in Old remain separate obligations. In particular,
common part labels alone do not prove vertexwise agreement or
root factorization. This module does not claim the universal
j-to-j+1 Picture theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- A factor of an ORDINARY homomorphism-embedding is again an
ordinary homomorphism-embedding when both factors are positive.
No closure-description assumptions and no global injectivity. -/
theorem ordinaryHE_first_factor_of_positive_composite
    {X Y Z : Type v}
    {A : RelStructure L X} {B : RelStructure L Y} {C : RelStructure L Z}
    {p : X → Y} {q : Y → Z}
    (hp : A.IsHomomorphism B p)
    (hq : B.IsHomomorphism C q)
    (hcomp : A.IsHomomorphismEmbedding C (q ∘ p)) :
    A.IsHomomorphismEmbedding B p := by
  refine ⟨hp, ?_⟩
  intro S hIrr
  obtain ⟨e, he⟩ := hcomp.embeddingOn S hIrr
  let d : Embedding (A.induce S) B := {
    toFun := fun x => p x.1
    injective := by
      intro x y hxy
      apply e.injective
      rw [he x, he y]
      exact congrArg q hxy
    map_rel_iff := by
      intro R xs
      constructor
      · intro htgt
        have htgtC : C.rel R (q ∘ p ∘ (Subtype.val ∘ xs)) :=
          hq R (p ∘ (Subtype.val ∘ xs)) htgt
        have hEq :
            (e ∘ xs) = q ∘ p ∘ (Subtype.val ∘ xs) := by
          funext i
          exact he (xs i)
        have htgtE : C.rel R (e ∘ xs) := by
          rw [hEq]
          exact htgtC
        exact (e.map_rel_iff R xs).mp htgtE
      · intro hsrc
        exact hp R (Subtype.val ∘ xs) hsrc
  }
  exact ⟨d, fun _ => rfl⟩

variable {P Q V I : Type v} {N : ℕ}

/-- Coordinate evaluation of an ACTUAL induced partite power is
an ORDINARY homomorphism-embedding to its selected old support.
This uses partite reflection of irreducibles, not any tagged
closure test or any ordinary injectivity assumption. -/
theorem native2019_coordinate_isOrdinaryHE_on_restriction
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (k : Fin N) :
    ((power (Old.restrict alpha) N).toRelStructure).IsHomomorphismEmbedding
      (Old.restrict alpha).toRelStructure
      (fun z => z.coord k) := by
  let R := Old.restrict alpha
  have hN : 0 < N := Nat.zero_lt_of_lt k.isLt
  have hPowerPart :
      ((power R N).toRelStructure).IsHomomorphismEmbedding
        A (power R N).part :=
    power_isPartiteOver hRestricted hN
  have hEq :
      R.part ∘ (fun z : NonInduced.Vertex R N => z.coord k) =
        (power R N).part := by
    funext z
    exact z.belongs k
  have hComp :
      ((power R N).toRelStructure).IsHomomorphismEmbedding A
        (R.part ∘ (fun z => z.coord k)) := by
    rw [hEq]
    exact hPowerPart
  exact ordinaryHE_first_factor_of_positive_composite
    (coordinate_homomorphism R k) hRestricted.1 hComp

/-- In the actual native attachment, the selected-coordinate/identity
fold is an ORDINARY homomorphism-embedding to Old when all selected
lines use the chosen parameter coordinate. This construction does
not need U-closedness of the whole attachment. -/
theorem native2019_selected_coordinate_isOrdinaryHE
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (J : Finset I) (k : Fin N)
    (hParameters : ∀ i ∈ J, (lines i).symbol k = .parameter) :
    (selectedNativeHJAttachment2019 Old alpha A hRestricted lines J).IsHomomorphismEmbedding
      Old.toRelStructure
      (selectedNativeHJCoordinateMap2019 Old alpha J k) := by
  classical
  let R := Old.restrict alpha
  let Core := (power R N).toRelStructure
  let maps := closureLineMaps Old alpha A hRestricted lines
  let Jset : Set I := (↑J : Set I)
  let mapsRest : Jset → Embedding (Old.toRelStructure.induce
      (Old.support alpha)) Core :=
    fun i => maps i.1
  let r : NonInduced.Vertex R N → V := fun z => (z.coord k).1
  have hCoord :
      Core.IsHomomorphismEmbedding R.toRelStructure
        (fun z => z.coord k) :=
    native2019_coordinate_isOrdinaryHE_on_restriction
      Old alpha A hRestricted k
  have hInc :
      R.toRelStructure.IsHomomorphismEmbedding Old.toRelStructure
        (fun x => x.1) :=
    (inclusion Old.toRelStructure (Old.support alpha)).isHomomorphismEmbedding
  have hCore : Core.IsHomomorphismEmbedding Old.toRelStructure r :=
    hInc.comp hCoord
  have hInverse : ∀ i : Jset, ∀ x : Old.support alpha,
      r (mapsRest i x) = x.1 := by
    intro i x
    change ((NonInduced.lineMap (lines i.1) x).coord k).1 = x.1
    rw [coordinate_lineMap_parameter
      (lines i.1) k (hParameters i.1 i.2) x]
  let pCopy : Jset → Embedding Old.toRelStructure Old.toRelStructure :=
    fun _ => Embedding.id Old.toRelStructure
  have hFold :
      (RelStructure.Attachment.attach Old.toRelStructure
        (Old.support alpha) Core mapsRest).IsHomomorphismEmbedding
      Old.toRelStructure
      (RelStructure.Attachment.fold r (fun i => pCopy i)) :=
    RelStructure.Attachment.fold_isHomomorphismEmbedding
      (Base := Old.toRelStructure) (S := Old.support alpha)
      (Core := Core) (f := mapsRest) (Q := Old.toRelStructure)
      r pCopy hInverse hCore
  change
    (RelStructure.Attachment.attach Old.toRelStructure
      (Old.support alpha) Core mapsRest).IsHomomorphismEmbedding
        Old.toRelStructure
        (RelStructure.Attachment.fold r
          (fun (_ : Jset) (x : V) => x))
  exact hFold

/-- The exact ordinary-map configuration needed by maximal-rank
two-side completion: every minimal bad native line family has
rest/single side ordinary HEs into Old at different coordinates,
with IDENTICAL Old part labels on the common power core.

Still required for general j-to-j+1: a proper free cut of each
tested closed source and two root embeddings of a fixed closed A
making those side maps compatible. -/
theorem exists_minimal_transverse_two_side_ordinaryHE_2019
    [DecidableEq I]
    (Old : System L P V) (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (S : Finset I)
    (hBad : ¬ ∃ k : Fin N,
      ∀ i ∈ S, (lines i).symbol k = .parameter) :
    ∃ T : Finset I, T ⊆ S ∧
      (¬ ∃ k : Fin N, ∀ i ∈ T,
        (lines i).symbol k = .parameter) ∧
      (∀ i ∈ T, ∃ kRest kOne : Fin N,
        (lines i).symbol kRest ≠ .parameter ∧
        (lines i).symbol kOne = .parameter ∧
        (selectedNativeHJAttachment2019
          Old alpha A hRestricted lines (T.erase i)).IsHomomorphismEmbedding
          Old.toRelStructure
          (selectedNativeHJCoordinateMap2019 Old alpha (T.erase i) kRest) ∧
        (selectedNativeHJAttachment2019
          Old alpha A hRestricted lines {i}).IsHomomorphismEmbedding
          Old.toRelStructure
          (selectedNativeHJCoordinateMap2019 Old alpha {i} kOne) ∧
        (∀ z : NonInduced.Vertex (Old.restrict alpha) N,
          Old.part (z.coord kRest).1 = Old.part (z.coord kOne).1)) := by
  obtain ⟨T, hTSub, hNoCommon, hLocal⟩ :=
    exists_minimal_noncommon_HJ_lines lines S hBad
  refine ⟨T, hTSub, hNoCommon, ?_⟩
  intro i hi
  obtain ⟨kRest, hConst, hRest⟩ := hLocal i hi
  obtain ⟨kOne, hOne⟩ := (lines i).hasParameter
  have hSingle : ∀ t ∈ ({i} : Finset I),
      (lines t).symbol kOne = .parameter := by
    intro t ht
    have hti : t = i := Finset.mem_singleton.mp ht
    subst t
    exact hOne
  exact ⟨kRest, kOne, hConst, hOne,
    native2019_selected_coordinate_isOrdinaryHE
      Old alpha A hRestricted lines (T.erase i) kRest hRest,
    native2019_selected_coordinate_isOrdinaryHE
      Old alpha A hRestricted lines {i} kOne hSingle,
    fun z => nativePower_two_coordinates_old_parts_agree
      Old alpha N z kRest kOne⟩

end AllThoseRamseyClasses.Published
