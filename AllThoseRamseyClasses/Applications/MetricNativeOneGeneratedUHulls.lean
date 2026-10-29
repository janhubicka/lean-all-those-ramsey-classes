import PartiteConstruction.Functional.NativeUClosedExactDictionary
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# One-generated canonical 2019 U-hulls contain every native function output

The exact positive-function-arity dictionary from the shared
partite-construction library proves that a subset of native
functional source vertices is closed under all ORIGINAL
functions exactly when it is an U-substructure of the
canonical root-pattern tagged relational encoding.

The algebraic UClosureHull is the least U-substructure
containing its seed. Therefore the canonical U-hull of
one source vertex is genuinely CLOSED under every original
native function, without first assuming that any small
function-closed subset exists. The conclusion holds for
multivalued native functions too, provided arities are
positive.

If the native functions are singleton-valued, the tagged
relational source is U-closed, and the induced ORIGINAL
one-generator U-hull is itself U-closed and intrinsically
U-irreducible by the already verified exact 2019 library
lemma. These are the precise two structural facts used
by corrected Definition 2.17(4b).

This is a source dictionary for the CANONICAL encoding.
It does not silently assert that an arbitrary weak metric
candidate uses this exact root-pattern representation
or that membership in the metric functional lift is
equivalent to native Option-valued F_j laws. The latter
source-matched transfer and the published cycle-compression
cutoff remain separate validation obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v

/-- The actual generated U-hull of a vertex in the tagged
positive-arity function representation is closed under
EVERY native function, without bounding its size. -/
theorem nativeOneGenerated_UHull_isClosed
    {L : Language.{u}} {V : Type v}
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity) (a : V) :
    A.IsClosed
      (UClosureHull L.patternClosureRules
        (patternTagExpansion A.patternGraph) {a}) := by
  apply
    (StructuralRamsey.Structure.isClosed_iff_taggedPattern_isUSubstructure
      A hPos
      (UClosureHull L.patternClosureRules
        (patternTagExpansion A.patternGraph) {a})).2
  exact UClosureHull_isUSubstructure
    L.patternClosureRules (patternTagExpansion A.patternGraph) {a}

/-- For a singleton-valued native source, the ORIGINAL
induced singleton U-hull of its tagged relational encoding
is simultaneously U-closed and U-irreducible. -/
theorem nativeOneGenerated_UHull_closed_irreducible
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (hSingle : A.SingletonValued) (a : V) :
    IsUClosed L.patternClosureRules
      ((patternTagExpansion A.patternGraph).induce
        (UClosureHull L.patternClosureRules
          (patternTagExpansion A.patternGraph) {a})) ∧
    IsUIrreducible L.patternClosureRules
      ((patternTagExpansion A.patternGraph).induce
        (UClosureHull L.patternClosureRules
          (patternTagExpansion A.patternGraph) {a})) := by
  have hAmbient : IsUClosed L.patternClosureRules
      (patternTagExpansion A.patternGraph) :=
    patternTagExpansion_isUClosed A hSingle
  exact ⟨hAmbient.induce_UClosureHull {a},
    hAmbient.singleton_hull_isUIrreducible a⟩

end AllThoseRamseyClasses.Applications.MetricSaturation
