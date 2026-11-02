import AllThoseRamseyClasses.Lifts.EHNFiveCycleImageFamilyConnected
import PartiteConstruction.Functional.DirectWeakIteration
import Mathlib.Tactic

/-!
# Track D: no injective forbidden EHN replacement in the C5/T target

The previous `EHNFiveCycleImageClosedFamily` theorem rules out
FULL forbidden embeddings. That is not enough to refute the printed
blanket injectivization step: a forbidden structure may be reducible,
and an injective homomorphism-embedding need not be full.

We close this exact logical gap for the family of all vertex- and
tuple-surjective original-partial HE images of C5. Every proper
three-colouring of C5 uses all three colours and has a source edge
between the preimages of ANY two distinct target colours.

Suppose a family member P has an INJECTIVE native EHN map g into
the 3-point target with an extra T(0,1,2). The composite
C5 -> P -> Fin 3 is a proper 3-colouring. The edge-coverage
certificate and injectivity of g imply every pair of distinct
vertices of P appears in a positive binary relation tuple.
Therefore P.graph is irreducible, hence P is a genuinely
function-language irreducible source.

By the very definition of an EHN map, its restriction to all
of P is then a FULL embedding, contradicting the independently
verified absence of any forbidden full embedding into the target.
This proves the exact no-INJECTIVE-EHN-replacement statement,
not merely no full embedding.

The source-generated image family is finite and connected and
satisfies printed tuple-surjective image closure; the target is
NOT claimed to be a free amalgam of two F-free maximal-lift
witnesses. No result about unrestricted Section 3 strong AP is
asserted or hidden in this certificate.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- A proper 3-colouring of the odd 5-cycle has a positively
related source pair mapping to EVERY pair of distinct target
colours. Symmetry of the old edge relation is included.
This is stronger than merely using all three colours. -/
theorem cycle5_properThreeColouring_coversAllEdges :
    ∀ c : Fin 5 → Fin 3,
      (∀ a b : Fin 5, cycle5Edge a b → c a ≠ c b) →
      ∀ u v : Fin 3, u ≠ v →
        ∃ a b : Fin 5,
          cycle5Edge a b ∧ c a = u ∧ c b = v := by
  decide

private def pEdge0 :
    Fin (language.graph.arity (.inl false)) := ⟨0, by decide⟩

private def pEdge1 :
    Fin (language.graph.arity (.inl false)) := ⟨1, by decide⟩

/-- If a forbidden C5-image P injectively weakly EHN-maps
into the 3-point target, all distinct pairs of vertices of
P belong to positive binary P-tuples. The source cyclic
colouring must realize every target colour-pair. -/
theorem fiveCycleImageFamily_graphIrreducible_of_injectiveEHN
    {X : Type} (P : Structure language X)
    (hP : fiveCycleImageFamily P)
    (g : X → Fin 3)
    (hg : P.IsEHNHomomorphismEmbedding triangleExtraTernary g)
    (hInj : Function.Injective g) :
    P.graph.Irreducible := by
  obtain ⟨f, _, hfHE, _⟩ := hP
  have hProper :
      ∀ a b : Fin 5, cycle5Edge a b →
        g (f a) ≠ g (f b) := by
    intro a b hab
    let xs : Fin (language.relArity false) → Fin 5 :=
      fun i => if i.val = 0 then a else b
    have hOld : cycle5.rel false xs := by
      change cycle5Edge (xs 0) (xs 1)
      simpa [xs] using hab
    have hPRel : P.rel false (f ∘ xs) :=
      hfHE.1.1 false xs hOld
    have hTarget :
        triangleExtraTernary.rel false (g ∘ (f ∘ xs)) :=
      hg.1.1 false (f ∘ xs) hPRel
    change triangleEdge (g (f a)) (g (f b)) at hTarget
    exact hTarget
  intro u v hne
  have hDistinctColours : g u ≠ g v := by
    intro h
    exact hne (hInj h)
  obtain ⟨a, b, hab, hga, hgb⟩ :=
    cycle5_properThreeColouring_coversAllEdges
      (fun z => g (f z)) hProper (g u) (g v) hDistinctColours
  have hfa : f a = u := hInj hga
  have hfb : f b = v := hInj hgb
  let sourceTuple : Fin (language.relArity false) → Fin 5 :=
    fun i => if i.val = 0 then a else b
  have hOld : cycle5.rel false sourceTuple := by
    change cycle5Edge (sourceTuple 0) (sourceTuple 1)
    simpa [sourceTuple] using hab
  have hPRel : P.rel false (f ∘ sourceTuple) :=
    hfHE.1.1 false sourceTuple hOld
  let tuple : Fin (language.graph.arity (.inl false)) → X :=
    fun i => if i.val = 0 then f a else f b
  have hGraphRel : P.graph.rel (.inl false) tuple := by
    change P.rel false tuple
    simpa [tuple, sourceTuple, Function.comp_def] using hPRel
  have hAt0 : tuple pEdge0 = u := by
    simpa [tuple, pEdge0] using hfa
  have hAt1 : tuple pEdge1 = v := by
    simpa [tuple, pEdge1] using hfb
  exact ⟨.inl false, tuple, pEdge0, pEdge1,
    hGraphRel, hAt0, hAt1⟩

/-- There is NO injective native EHN map from ANY member of
the printed-image-closed forbidden family to the three-vertex
target containing the extra ternary tuple.

This is stronger than `noFullMember`: the source member P
need not have been assumed irreducible. It becomes irreducible
from its existence as an injectively represented 3-colour
quotient of the odd cycle. -/
theorem fiveCycleImageFamily_noInjectiveEHN
    {X : Type} (P : Structure language X)
    (hP : fiveCycleImageFamily P)
    (g : X → Fin 3)
    (hg : P.IsEHNHomomorphismEmbedding triangleExtraTernary g) :
    ¬ Function.Injective g := by
  intro hInjective
  have hGraph : P.graph.Irreducible :=
    fiveCycleImageFamily_graphIrreducible_of_injectiveEHN
      P hP g hg hInjective
  have hNative : P.Irreducible :=
    irreducible_of_graph_irreducible P hGraph
  obtain ⟨e, _⟩ := hg.2 P hNative (Structure.Embedding.id P)
  have hForbiddenFull :
      ContainsFullForbiddenSubstructure
        (L := language) fiveCycleImageFamily
        triangleExtraTernary :=
    ⟨X, P, hP, ⟨e⟩⟩
  exact fiveCycleImageFamily_noFullMember_in_triangleExtraTernary
    hForbiddenFull

/-- Fully scoped counterexample to the GENERAL printed
injectivization inference, not to the stronger maximal-lift
free-amalgamation lemma. The family is finite/connected and
closed under the printed tuple-surjective HE image condition.
The target has a noninjective forbidden native EHN witness,
and there is NO injective forbidden EHN replacement from any
member of the family. -/
theorem fiveCycleImageFamily_counterexample_to_blanketInjectivization :
    HasTupleSurjectiveForbiddenImageClosure
      (L := language) fiveCycleImageFamily ∧
    GlobalForbiddenSourcesConnectedNonempty
      (L := language) fiveCycleImageFamily ∧
    (∀ {X : Type} (P : Structure language X),
      fiveCycleImageFamily P → Finite X) ∧
    fiveCycleImageFamily cycle5 ∧
    cycle5.IsEHNHomomorphismEmbedding
      triangleExtraTernary weakColor ∧
    ¬ Function.Injective weakColor ∧
    (∀ {X : Type} (P : Structure language X)
      (g : X → Fin 3),
      fiveCycleImageFamily P →
      P.IsEHNHomomorphismEmbedding triangleExtraTernary g →
      ¬ Function.Injective g) := by
  exact ⟨fiveCycleImageFamily_printedImageClosed,
    fiveCycleImageFamily_connectedNonempty,
    fun P hP => finite_of_fiveCycleImageFamily P hP,
    cycle5_mem_imageFamily,
    weakColor_nativeEHN,
    weakColor_not_injective,
    fun P g hP hg => fiveCycleImageFamily_noInjectiveEHN
      P hP g hg⟩

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
