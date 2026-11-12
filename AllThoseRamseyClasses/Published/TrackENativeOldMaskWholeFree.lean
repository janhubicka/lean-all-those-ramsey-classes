import AllThoseRamseyClasses.Published.TrackENativeOldMaskDomainFree
import PartiteConstruction.Functional.WholeMaskTagFreeAmalgam2019
import PartiteConstruction.Functional.WholeMaskCanonicalFullEmbeddingForward2019

/-!
# Track E2: genuine native free amalgams preserve the FULL original OLD mask graph

We complete both relation cases, not merely the active input domains:

* ORIGINAL OLD complete output-part domain masks localize through
  genuine FULL native functional free sides (preceding lemma).
* An ORIGINAL complete output tuple has the ENTIRE original native
  set-valued value as one Option(Set) fibre. Once the root has
  localized to a side, the full embedding equation identifies the
  entire target value with the image of the side value. EVERY
  enumerated output therefore has a source-side preimage.
  Transversality/part-preservation preserves the exact output
  label assigned to each enumeration slot.

Thus the canonical OLD complete-mask graph of a native functional
free amalgam is itself a genuine relational free amalgam on the
identical vertex set and the identical full side maps. The pinned
2019 wholeMaskTagExpansion free-amalgam theorem then adds the fresh
original full OLD closure-root tags without changing the diagram.

This is the critical missing source-side bridge for assembling
the actual single split/mask hybrid picture. It does not introduce
a weak source closure hull, infer full definedness reflection from
a source-defined projection, or assert that arbitrary intermediate
hybrid tagged targets decode or possess a strict mixed-root
completion. Those remain separate E2 steps.

The proof works with all original primitive arities, repeated input
vertices, positive and empty complete-output masks, and arbitrary
finite/infinite carrier types. A genuinely defined-empty Option(Set)
state is not introduced by native toNonemptyPartial, so a complete
empty-output relation cannot arise without positive native output.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.RelStructure
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {H E F C : Type w}

/-- Full genuine native part-preserving embeddings induce full
original complete-output-mask OLD relational embeddings on exactly
the same vertex maps. This is the full forward 2019 encoding,
not a source-defined weak projection. -/
noncomputable def nativeOriginalWholeMaskOldEmbedding
    {X Y : Type w}
    {A : FunctionalPartite.System L Parts X}
    {B : FunctionalPartite.System L Parts Y}
    (e : FunctionalPartite.Embedding A B) :
    RelStructure.Embedding
      (A.toStructure.toNonemptyPartial.wholeMaskPatternGraph A.part)
      (B.toStructure.toNonemptyPartial.wholeMaskPatternGraph B.part) :=
  (e.toEmbedding.toNonemptyPartial).wholeMaskPatternGraph
    A.part B.part e.map_part

/-- Once an original whole-mask INPUT ROOT localizes to a full
partite side, EVERY output of its complete multivalued value
localizes to that SAME side, with all output-part labels intact.

The side root is obtained from the exact old-domain localization.
No output points are discarded or inserted. -/
private theorem originalWholeMaskOutput_factorFullSide
    {X Y : Type w}
    {Source : FunctionalPartite.System L Parts X}
    {Whole : FunctionalPartite.System L Parts Y}
    (e : FunctionalPartite.Embedding Source Whole)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts Parts)
    (z : Fin (p.rootSize + q.size) → Y)
    (hz : (Whole.toStructure.toNonemptyPartial.wholeMaskPatternGraph
      Whole.part).rel (.inr (.inr (p, q))) z)
    (r : Fin p.rootSize → X)
    (hDomain : (Source.toStructure.toNonemptyPartial.wholeMaskPatternGraph
      Source.part).rel (.inr (.inl (p, q))) r)
    (hRoot : (fun i : Fin p.rootSize =>
      z (Fin.castAdd q.size i)) = e.toEmbedding.toFun ∘ r) :
    ∃ (x : Fin (p.rootSize + q.size) → X),
      (Source.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Source.part).rel (.inr (.inr (p, q))) x ∧
      z = e.toEmbedding.toFun ∘ x := by
  classical
  let input : Fin p.rootSize → Y :=
    fun i => z (Fin.castAdd q.size i)
  let output : Fin q.size → Y :=
    fun j => z (Fin.natAdd p.rootSize j)
  have hWhole :
      Function.Injective input ∧
      Whole.toStructure.toNonemptyPartial.func
        p.symbol (input ∘ p.argMap) = some (Set.range output) ∧
      (∀ j : Fin q.size, Whole.part (output j) = q.label j) := hz
  have hSide :
      Function.Injective r ∧
      ∃ T : Set X,
        Source.toStructure.toNonemptyPartial.func
          p.symbol (r ∘ p.argMap) = some T ∧
        Source.part '' T = Set.range q.label := hDomain
  obtain ⟨hrInj, T, hSrcVal, _hParts⟩ := hSide
  have hInputMapped :
      e.toEmbedding.toFun ∘ (r ∘ p.argMap) =
        input ∘ p.argMap := by
    funext i
    exact (congrFun hRoot (p.argMap i)).symm
  have hMapped := (e.toEmbedding.toNonemptyPartial).map_func
    p.symbol (r ∘ p.argMap)
  rw [hSrcVal] at hMapped
  have hValueMap :
      some (Structure.imageSet e.toEmbedding.toFun T) =
      Whole.toStructure.toNonemptyPartial.func
        p.symbol (e.toEmbedding.toFun ∘ (r ∘ p.argMap)) := hMapped
  have hWholeMapped :
      Whole.toStructure.toNonemptyPartial.func
        p.symbol (e.toEmbedding.toFun ∘ (r ∘ p.argMap)) =
        some (Set.range output) := by
    rw [hInputMapped]
    exact hWhole.2.1
  have hImage : Structure.imageSet e.toEmbedding.toFun T =
      Set.range output :=
    Option.some.inj (hValueMap.trans hWholeMapped)
  have hPre (j : Fin q.size) :
      ∃ a : X, a ∈ T ∧ output j = e.toEmbedding.toFun a := by
    have hout : output j ∈ Set.range output := ⟨j, rfl⟩
    rw [← hImage] at hout
    obtain ⟨a, ha, hEq⟩ := hout
    exact ⟨a, ha, hEq.symm⟩
  let out : Fin q.size → X := fun j => Classical.choose (hPre j)
  have houtMem (j : Fin q.size) : out j ∈ T :=
    (Classical.choose_spec (hPre j)).1
  have houtEq (j : Fin q.size) :
      output j = e.toEmbedding.toFun (out j) :=
    (Classical.choose_spec (hPre j)).2
  have houtPart (j : Fin q.size) :
      Source.part (out j) = q.label j := by
    calc
      Source.part (out j) = Whole.part (e (out j)) :=
        (e.map_part (out j)).symm
      _ = Whole.part (output j) :=
        congrArg Whole.part (houtEq j).symm
      _ = q.label j := hWhole.2.2 j
  have hRange : Set.range out = T := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact houtMem j
    · intro ha
      have he : e.toEmbedding.toFun a ∈
          Structure.imageSet e.toEmbedding.toFun T := ⟨a, ha, rfl⟩
      rw [hImage] at he
      obtain ⟨j, hj⟩ := he
      refine ⟨j, ?_⟩
      apply e.toEmbedding.injective
      calc
        e.toEmbedding.toFun (out j) = output j := (houtEq j).symm
        _ = e.toEmbedding.toFun a := hj
  have hSrcRange :
      Source.toStructure.toNonemptyPartial.func
        p.symbol (r ∘ p.argMap) = some (Set.range out) := by
    rw [hRange]
    exact hSrcVal
  let x : Fin (p.rootSize + q.size) → X :=
    Fin.append r out
  have hx :
      (Source.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Source.part).rel (.inr (.inr (p, q))) x := by
    change
      Function.Injective
        (fun i : Fin p.rootSize => x (Fin.castAdd q.size i)) ∧
      Source.toStructure.toNonemptyPartial.func p.symbol
        ((fun i : Fin p.rootSize =>
            x (Fin.castAdd q.size i)) ∘ p.argMap) =
          some (Set.range (fun j : Fin q.size =>
            x (Fin.natAdd p.rootSize j))) ∧
      (∀ j : Fin q.size,
        Source.part (x (Fin.natAdd p.rootSize j)) = q.label j)
    simpa only [x, Fin.append_left, Fin.append_right] using
      (show Function.Injective r ∧
        Source.toStructure.toNonemptyPartial.func
          p.symbol (r ∘ p.argMap) = some (Set.range out) ∧
        (∀ j : Fin q.size, Source.part (out j) = q.label j)
       from ⟨hrInj, hSrcRange, houtPart⟩)
  refine ⟨x, hx, ?_⟩
  funext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    change input i = e.toEmbedding.toFun (r i)
    exact congrFun hRoot i
  · intro j
    change output j = e.toEmbedding.toFun (out j)
    exact houtEq j

/-- The COMPLETE original multivalued output-tuple relation case of
the actual native-to-OLD free-amalgamation theorem. The active input
root chooses one full native side via the previous certified/proposed
domain lemma, and exact full whole-value reflection puts ALL output
coordinates on that same side. No disjointness of inputs and outputs
or singleton-source assumption. -/
theorem nativeFreeAmalgam_originalWholeMaskOutput_side
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding)
    (p : Language.FunctionInputPattern L)
    (q : Language.CompleteOutputParts Parts)
    (z : Fin (p.rootSize + q.size) → C)
    (hz : (Whole.toStructure.toNonemptyPartial.wholeMaskPatternGraph
      Whole.part).rel (.inr (.inr (p, q))) z) :
    (∃ x : Fin (p.rootSize + q.size) → E,
      (Left.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Left.part).rel (.inr (.inr (p, q))) x ∧
      z = iL.toEmbedding.toFun ∘ x) ∨
    (∃ x : Fin (p.rootSize + q.size) → F,
      (Right.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Right.part).rel (.inr (.inr (p, q))) x ∧
      z = iR.toEmbedding.toFun ∘ x) := by
  let root : Fin p.rootSize → C :=
    fun i => z (Fin.castAdd q.size i)
  have hDom :
      (Whole.toStructure.toNonemptyPartial.wholeMaskPatternGraph
        Whole.part).rel (.inr (.inl (p, q))) root :=
    Whole.toStructure.toNonemptyPartial.wholeMaskPatternGraph_output_has_domain
      Whole.part p q z hz
  rcases nativeFreeAmalgam_originalWholeMaskDomain_side
      hFree p q root hDom with
    ⟨r, hRoot, hEq⟩ | ⟨r, hRoot, hEq⟩
  · exact Or.inl <| originalWholeMaskOutput_factorFullSide
      iL p q z hz r hRoot hEq
  · exact Or.inr <| originalWholeMaskOutput_factorFullSide
      iR p q z hz r hRoot hEq

/-- The entire ORIGINAL complete-mask relational graph of an actual
FULL native partite free amalgam forms a genuine relational free
amalgam on the SAME vertex carriers and side maps.

The three relation cases are the native primitive relation tuples,
complete OLD active domains, and complete OLD output tuples.
The reverse implications use FULL induced original OLD embeddings,
not merely positive homomorphisms. -/
theorem nativeFreeAmalgam_originalWholeMaskGraph
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding) :
    RelStructure.IsFreeAmalgam
      (nativeOriginalWholeMaskOldEmbedding sL)
      (nativeOriginalWholeMaskOldEmbedding sR)
      (nativeOriginalWholeMaskOldEmbedding iL)
      (nativeOriginalWholeMaskOldEmbedding iR) := by
  classical
  refine {
    covers := hFree.covers
    overlap := hFree.overlap
    rel_iff := ?_
  }
  intro R z
  rcases R with R | R
  · exact hFree.rel_iff R z
  · rcases R with pq | pq
    · rcases pq with ⟨p, q⟩
      constructor
      · exact nativeFreeAmalgam_originalWholeMaskDomain_side
          hFree p q z
      · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
        · exact ((nativeOriginalWholeMaskOldEmbedding iL).map_rel_iff
            (.inr (.inl (p, q))) r).mpr hr
        · exact ((nativeOriginalWholeMaskOldEmbedding iR).map_rel_iff
            (.inr (.inl (p, q))) r).mpr hr
    · rcases pq with ⟨p, q⟩
      constructor
      · exact nativeFreeAmalgam_originalWholeMaskOutput_side
          hFree p q z
      · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
        · exact ((nativeOriginalWholeMaskOldEmbedding iL).map_rel_iff
            (.inr (.inr (p, q))) r).mpr hr
        · exact ((nativeOriginalWholeMaskOldEmbedding iR).map_rel_iff
            (.inr (.inr (p, q))) r).mpr hr

/-- The original 2019 FULL old-root tagged complete-output-mask
component is free on every actual native FULL functional partite
free-amalgamation diagram, by the already validated general
wholeMaskTagExpansion free-amalgam functor.

This supplies the OLD half of the canonical split/mask base hybrid
source free-amalgamation, not arbitrary hybrid target decoding or
the two-pass sparse E2 Ramsey object. -/
theorem nativeFreeAmalgam_originalWholeMaskTagged
    {Root : FunctionalPartite.System L Parts H}
    {Left : FunctionalPartite.System L Parts E}
    {Right : FunctionalPartite.System L Parts F}
    {Whole : FunctionalPartite.System L Parts C}
    {sL : FunctionalPartite.Embedding Root Left}
    {sR : FunctionalPartite.Embedding Root Right}
    {iL : FunctionalPartite.Embedding Left Whole}
    {iR : FunctionalPartite.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam
      sL.toEmbedding sR.toEmbedding
      iL.toEmbedding iR.toEmbedding) :
    RelStructure.IsFreeAmalgam
      (nativeOriginalWholeMaskOldEmbedding sL).wholeMaskTag
      (nativeOriginalWholeMaskOldEmbedding sR).wholeMaskTag
      (nativeOriginalWholeMaskOldEmbedding iL).wholeMaskTag
      (nativeOriginalWholeMaskOldEmbedding iR).wholeMaskTag :=
  (nativeFreeAmalgam_originalWholeMaskGraph hFree).wholeMaskTagExpansion

end AllThoseRamseyClasses.Published
