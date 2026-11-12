import AllThoseRamseyClasses.Published.TrackEOldSplitHybridCanonical
import PartiteConstruction.Functional.WholeMaskPartPreservingEmbeddingEquiv2019
import PartiteConstruction.Functional.TrackENativePartialFullFaithfulness

/-!
# Track E2: canonical hybrid encoding is FULLY FAITHFUL for finite native partite Systems

The canonical hybrid language has three components:
(1) original complete-output OLD domain/value/root relations,
(2) singleton output-part positive graph/root relations,
(3) unary vertex-part predicates including isolated vertices.

The merged forward functor sends every FULL native part-preserving
functional embedding to a FULL relational embedding of canonical
hybrid sources, with exactly the same underlying vertex map.

We prove its converse: a FULL relational embedding of two canonical
finite hybrid sources reflects every original complete OLD mask and
value, and hence decodes to a FULL native function embedding on
the SAME map. The unary predicates enforce preservation of the
part of EVERY vertex. This is not a weak EHN map: undefined
source function inputs reflect the target's domain in the FULL
embedding category.

The proof uses the verified original OLD complete-mask decoder,
the canonical value/definedness round trip, and the pinned exact
full-faithfulness of native toNonemptyPartial. It does NOT assume
that an arbitrary noncanonical intermediate hybrid relational
Picture already decodes coherently to a native System.

Consequently full native partite embedding sets and full
relational embedding sets of their canonical hybrid presentations
are literally equivalent, composition-naturally, with no new
vertices, carrier reindexing, change of parts, or closure hull.

This prepares class strong-amalgamation and Ramsey-arrow transfer,
but does not construct a hybrid sparse ordered Ramsey witness or
prove coherent decoding of arbitrary B-covered noncanonical targets.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The faithful native Option(Set) encoding of a genuinely
transversal native partite System also has transversal whole
Option values. Source-defined and undefined cases are kept
distinct; native operations cannot be independently defined-empty. -/
private theorem nativeHybrid_partialFibreTransversal
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    FibreTransversal A.toStructure.toNonemptyPartial A.part := by
  intro F xs T hDefined y hy z hz heq
  have hFibre : A.func F xs = T := by
    change (if (A.func F xs).Nonempty then
      some (A.func F xs) else none) = some T at hDefined
    by_cases h : (A.func F xs).Nonempty
    · simp only [if_pos h] at hDefined
      exact Option.some.inj hDefined
    · simp only [if_neg h] at hDefined
      cases hDefined
  rw [← hFibre] at hy hz
  exact A.funcTransversal F xs y z hy hz heq

/-- A FULL hybrid relational embedding between canonical genuine
finite native partite Systems recovers a genuine FULL native
part-preserving functional embedding on the literal same map.

The complete original OLD domain/value component prevents phantom
target function fibres; the unary part predicates force all vertex
parts, including isolated vertices. No weak source map or arbitrary
noncanonical target normalization is involved. -/
noncomputable def nativePartiteEmbedding_of_hybrid
    {X Y : Type w} [Finite X] [Finite Y]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y)
    (f : RelStructure.Embedding A.splitMaskHybrid B.splitMaskHybrid) :
    FunctionalPartite.Embedding A B := by
  classical
  let PA : PartialSetStructure L X := A.toStructure.toNonemptyPartial
  let PB : PartialSetStructure L Y := B.toStructure.toNonemptyPartial
  let Old : RelStructure (L.wholeMaskPatternLanguage Parts) Y :=
    PB.wholeMaskPatternGraph B.part
  have hTransA : FibreTransversal PA A.part :=
    nativeHybrid_partialFibreTransversal A
  have hTransB : FibreTransversal PB B.part :=
    nativeHybrid_partialFibreTransversal B
  let fOld : RelStructure.Embedding
      (PA.wholeMaskPatternGraph A.part) Old := {
    toFun := f
    injective := f.injective
    map_rel_iff := fun R xs => f.map_rel_iff (.inl (.inl R)) xs
  }
  have hUnique (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → Y)
      (U T : Set Y)
      (hU : HasWholeMaskValue Old F xs U)
      (hT : HasWholeMaskValue Old F xs T) : U = T := by
    have hu : PB.func F xs = some U :=
      (PB.hasWholeMaskValue_iff_source_func_some
        B.part hTransB F xs U).mp hU
    have ht : PB.func F xs = some T :=
      (PB.hasWholeMaskValue_iff_source_func_some
        B.part hTransB F xs T).mp hT
    exact Option.some.inj (hu.symm.trans ht)
  have hDomain (F : L.FuncSymbol)
      (xs : Fin (L.funcArity F) → Y) :
      Old.wholeMaskPartialDecode.Defined F xs ↔
        HasWholeMaskDomain Old F xs := by
    change (∃ U : Set Y,
      Old.wholeMaskPartialDecode.func F xs = some U) ↔ _
    rw [PB.wholeMaskPartialDecode_canonical_func
      B.part hTransB F xs]
    exact (PB.hasWholeMaskDomain_iff_sourceDefined
      B.part hTransB F xs).symm
  let fDecoded : PartialSetStructure.Embedding PA
      Old.wholeMaskPartialDecode :=
    PartialSetStructure.Embedding.ofWholeMaskPatternGraph
      PA A.part hTransA Old hUnique hDomain fOld
  let fPartial : PartialSetStructure.Embedding PA PB := {
    toFun := fDecoded.toFun
    injective := fDecoded.injective
    map_rel_iff := fDecoded.map_rel_iff
    map_func := by
      intro F xs
      have h := fDecoded.map_func F xs
      change (PA.func F xs).map
          (Structure.imageSet fDecoded.toFun) =
        Old.wholeMaskPartialDecode.func F (fDecoded.toFun ∘ xs) at h
      rw [PB.wholeMaskPartialDecode_canonical_func
        B.part hTransB F (fDecoded.toFun ∘ xs)] at h
      exact h
  }
  let fNative : Structure.Embedding A.toStructure B.toStructure :=
    partialFullEmbedding_toNative fPartial
  have hPart (x : X) : B.part (f x) = A.part x := by
    have h := (f.map_rel_iff (.inr (.inr (A.part x)))
      (fun _ : Fin 1 => x)).mpr
      (show A.splitMaskHybrid.rel (.inr (.inr (A.part x)))
        (fun _ : Fin 1 => x) from rfl)
    exact h
  exact {
    toEmbedding := fNative
    map_part := hPart
  }

/-- The canonical hybrid signature is a FULLY FAITHFUL presentation
of finite genuine native functional partite Systems. Every FULL
native embedding gives and is recovered from precisely one FULL
hybrid relational embedding, on the identical vertex function.

No extra part label is free to change, even for isolated vertices. -/
noncomputable def nativePartiteHybridFullEmbeddingEquiv
    {X Y : Type w} [Finite X] [Finite Y]
    (A : FunctionalPartite.System L Parts X)
    (B : FunctionalPartite.System L Parts Y) :
    FunctionalPartite.Embedding A B ≃
      RelStructure.Embedding A.splitMaskHybrid B.splitMaskHybrid where
  toFun := systemEmbedding_splitMaskHybrid
  invFun := nativePartiteEmbedding_of_hybrid A B
  left_inv := by
    intro e
    apply FunctionalPartite.Embedding.ext
    intro x
    rfl
  right_inv := by
    intro e
    apply RelStructure.Embedding.ext
    intro x
    rfl

end AllThoseRamseyClasses.Published
