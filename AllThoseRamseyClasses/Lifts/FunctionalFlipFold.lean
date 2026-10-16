import PartiteConstruction.Functional.WeakAttachment
import PartiteConstruction.Functional.FullFreeAmalgam
import PartiteConstruction.Iterated.FinalAttachment

/-!
# The weak functional fold needed for the piece flip

Given two full rooted structures P,Q over the same functional root,
a compatible pair of weak 2019-style homomorphism-embeddings to a
target folds over their canonical full functional free amalgam.
The result is a weak (EHN) functional homomorphism-embedding; neither
global injectivity nor surjectivity on arbitrary function fibres
is required.

This is the map-theoretic heart of the paper's flip. Membership of
the new amalgam in the forbidden family still depends on piece
equivalence and is NOT a consequence of this lemma.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {UR UP UQ UT : Type v}

/-- Fold of two compatible vertex maps on the concrete functional
free amalgam. It reuses the checked relational fold on the
function-graph encodings; the source amalgam itself is functional. -/
noncomputable def functionalFlipFold
    (Root : Structure L UR) (P : Structure L UP) (Q : Structure L UQ)
    (sP : Structure.Embedding Root P)
    (sQ : Structure.Embedding Root Q)
    (pP : UP → UT) (pQ : UQ → UT)
    (hcompat : ∀ r, pP (sP r) = pQ (sQ r)) :
    Structure.FreeAmalgam.Vertex Root P Q sP sQ → UT :=
  RelStructure.FreeAmalgam.fold
    (D := Root.graph) (A := P.graph) (B := Q.graph)
    (fA := sP.graph) (fB := sQ.graph)
    pP pQ hcompat

/-- The folded map extends the left rooted piece map exactly. -/
theorem functionalFlipFold_left
    (Root : Structure L UR) (P : Structure L UP) (Q : Structure L UQ)
    (sP : Structure.Embedding Root P)
    (sQ : Structure.Embedding Root Q)
    (pP : UP → UT) (pQ : UQ → UT)
    (hcompat : ∀ r, pP (sP r) = pQ (sQ r)) (x : UP) :
    functionalFlipFold Root P Q sP sQ pP pQ hcompat
      (Structure.FreeAmalgam.leftEmbedding Root P Q sP sQ x) = pP x :=
  RelStructure.FreeAmalgam.fold_left
    (D := Root.graph) (A := P.graph) (B := Q.graph)
    (fA := sP.graph) (fB := sQ.graph) pP pQ hcompat x

/-- The folded map extends the right-hand complement map exactly. -/
theorem functionalFlipFold_right
    (Root : Structure L UR) (P : Structure L UP) (Q : Structure L UQ)
    (sP : Structure.Embedding Root P)
    (sQ : Structure.Embedding Root Q)
    (pP : UP → UT) (pQ : UQ → UT)
    (hcompat : ∀ r, pP (sP r) = pQ (sQ r)) (x : UQ) :
    functionalFlipFold Root P Q sP sQ pP pQ hcompat
      (Structure.FreeAmalgam.rightEmbedding Root P Q sP sQ x) = pQ x :=
  RelStructure.FreeAmalgam.fold_right
    (D := Root.graph) (A := P.graph) (B := Q.graph)
    (fA := sP.graph) (fB := sQ.graph) pP pQ hcompat x

/-- The exact replacement-map lemma needed for a flip:
weak functional maps on each rooted side glue to a weak functional
map on the full source free amalgam. It preserves relation tuples,
positive function incidences, and full embeddings of every
functionally irreducible source substructure. -/
theorem functionalFlipFold_isEHNHomomorphismEmbedding
    (Root : Structure L UR) (P : Structure L UP) (Q : Structure L UQ)
    (Target : Structure L UT)
    (sP : Structure.Embedding Root P)
    (sQ : Structure.Embedding Root Q)
    (pP : UP → UT) (pQ : UQ → UT)
    (hcompat : ∀ r, pP (sP r) = pQ (sQ r))
    (hpP : P.IsEHNHomomorphismEmbedding Target pP)
    (hpQ : Q.IsEHNHomomorphismEmbedding Target pQ) :
    Structure.IsEHNHomomorphismEmbedding
      (Structure.FreeAmalgam.amalgam Root P Q sP sQ) Target
      (functionalFlipFold Root P Q sP sQ pP pQ hcompat) := by
  apply Structure.IsEHNHomomorphismEmbedding.of_freeAmalgam
    (Structure.FreeAmalgam.isFreeAmalgam Root P Q sP sQ)
    hpP hpQ
  · intro x
    exact functionalFlipFold_left Root P Q sP sQ pP pQ hcompat x
  · intro x
    exact functionalFlipFold_right Root P Q sP sQ pP pQ hcompat x

end AllThoseRamseyClasses.Lifts
