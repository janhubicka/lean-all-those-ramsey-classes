import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceFullFibres
import PartiteConstruction.Structure.Basic

/-!
# Genuine full functional embedding of incidence closures

The full incidence functions must be interpreted on EVERY input tuple
over the old/new carrier. A negative old tuple, or a tuple containing
a new incidence vertex, has the empty output fibre.

This module packages the verified exact image-of-fibre theorem and
injectivity into the upstream Structure.Embedding interface. It
uses a function-only reduct: relation symbols are included as inert,
always-false placeholders to keep a uniform universe-polymorphic
signature. The graph/tuple-order relations and prescribed total
vertex order of the paper require further work.

In particular, the structure is not assumed Ramsey and the
functional class-level strong amalgamation is not asserted.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Same finite arities as the original relation symbols, now used
as set-valued incidence-function symbols. The relation component
is deliberately inert in this functional reduct. -/
abbrev incidenceFunctionalLanguage (L : RelLanguage.{u}) :
    Language.{u} where
  RelSymbol := L.Symbol
  FuncSymbol := L.Symbol
  relArity := L.arity
  funcArity := L.arity

/-- The full set-valued incidence functions, on every tuple
of old and new vertices, in the upstream functional language. -/
def incidenceFunctionalReduct {L : RelLanguage.{u}}
    {V : Type v} (A : TotalOrderData L V) :
    Structure (incidenceFunctionalLanguage L) (IncidenceCarrier A) where
  rel := fun _ _ => False
  func := fullIncidenceFibre A

/-- The extension of any original full relational embedding is
a genuine full FUNCTIONAL embedding of the incidence reduct,
not merely a positive function-graph homomorphism. In particular
undefined and empty fibres are reflected on all mixed tuples. -/
noncomputable def incidenceFunctionalEmbedding
    {L : RelLanguage.{u}} {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Structure.Embedding (incidenceFunctionalReduct A)
      (incidenceFunctionalReduct B) where
  toFun := incidenceMap A B f hf
  injective := incidenceMap_injective A B f hf
  map_rel_iff := by
    intro R t
    exact Iff.rfl
  map_func := by
    intro F t
    exact incidenceMap_image_fullIncidenceFibre A B f hf F t

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
