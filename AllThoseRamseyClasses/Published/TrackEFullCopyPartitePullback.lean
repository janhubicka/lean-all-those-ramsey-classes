import PartiteConstruction.Functional.OutputPartSingletonization
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track E2: inherit genuine partite structure on any full ambient copy

An irreducible native test of the finite-family E2 weak-locality
condition is given as an arbitrary Structure E with a FULL embedding
e : E ↪ A into a partite ambient System A. It need not arrive with
a named part map.

The part map on E is canonically part_A ∘ e. Relational-tuple
transversality descends along full relation reflection and e.injective.
Function-fibre transversality descends along the full equality of
set-valued operation fibres and e.injective. Consequently E becomes
a genuine native FunctionalPartite.System on the SAME carrier, and e
becomes a full part-preserving System embedding. By the checked
output-part splitter, e also becomes a full embedding of the split
Systems with exactly the original vertex map.

No irreducibility, finite carrier, closure-hull, positivity or
undefined-domain reflection assumptions are introduced. This is a
reusable lemma for upgrading E2's full ambient irreducible-test clause.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.FunctionalPartite

universe u v w z
variable {L : Language.{u}} {Parts : Type v}

/-- Pull back the ambient vertex parts to an arbitrary full functional
substructure E. The transversality proofs use BOTH full primitive
relation reflection and full set-valued function-value equality. -/
def systemOnFullCopy
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) :
    FunctionalPartite.System L Parts VE where
  toStructure := E
  part x := A.part (e x)
  relTransversal := by
    intro R xs hRel i j hPart
    apply e.injective
    exact A.relTransversal R (e ∘ xs)
      ((e.map_rel_iff R xs).mpr hRel) i j hPart
  funcTransversal := by
    intro F xs y z hy hz hPart
    have hyA : e y ∈ A.func F (e ∘ xs) := by
      rw [← e.map_func F xs]
      exact ⟨y, hy, rfl⟩
    have hzA : e z ∈ A.func F (e ∘ xs) := by
      rw [← e.map_func F xs]
      exact ⟨z, hz, rfl⟩
    apply e.injective
    exact A.funcTransversal F (e ∘ xs)
      (e y) (e z) hyA hzA hPart

@[simp] theorem systemOnFullCopy_toStructure
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) :
    (systemOnFullCopy A E e).toStructure = E := rfl

@[simp] theorem systemOnFullCopy_part
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) (x : VE) :
    (systemOnFullCopy A E e).part x = A.part (e x) := rfl

/-- The source full native embedding becomes a full PART-PRESERVING
System embedding without changing any vertex or function value. -/
def systemOnFullCopy_embedding
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) :
    FunctionalPartite.Embedding (systemOnFullCopy A E e) A where
  toEmbedding := e
  map_part := fun _ => rfl

/-- Therefore the original full copy is also a full copy of the
canonical singleton output-part splits; the underlying vertex map
remains exactly e, including on source-isolated vertices. -/
def systemOnFullCopy_splitEmbedding
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure) :
    FunctionalPartite.Embedding
      (systemOnFullCopy A E e).splitOutputParts A.splitOutputParts :=
  (systemOnFullCopy_embedding A E e).splitOutputParts

@[simp] theorem systemOnFullCopy_splitEmbedding_apply
    {VA : Type w} {VE : Type z}
    (A : FunctionalPartite.System L Parts VA)
    (E : Structure L VE)
    (e : Structure.Embedding E A.toStructure)
    (x : VE) :
    systemOnFullCopy_splitEmbedding A E e x = e x := rfl

end AllThoseRamseyClasses.Published
