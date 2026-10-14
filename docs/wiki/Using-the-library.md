# Using the library

## Install and import

Pin a tested Git revision in a Lake dependency; do not depend on
floating main if reproducibility matters.

```toml
[[require]]
name = "lean-all-those-ramsey-classes"
git = "https://github.com/janhubicka/lean-all-those-ramsey-classes.git"
rev = "e185d6105ac80643bf81b1cc3c4cbd8d11eee6c0"
```

The pinned revision is the merged curated-API and wiki commit, whose
complete PR build and permitted-axiom audit passed in
[run 38639438183](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38639438183).
For future updates use a later SHA only after its full workflow passes.

```lean
import AllThoseRamseyClasses.PublicAPI
-- or: import AllThoseRamseyClasses.ApplicationsAPI
-- or: import AllThoseRamseyClasses
```

`PublicAPI` imports only the corrected core; `ApplicationsAPI` adds
completed Ramsey-class examples. The package pins its
`partite-construction` dependency in [lakefile.toml](../../lakefile.toml).

## Main reusable definitions

```lean
#check StructuralRamsey.RelLanguage
#check StructuralRamsey.RelStructure
#check StructuralRamsey.RelStructure.Embedding
#check StructuralRamsey.Arrow
#check StructuralRamsey.RelStructure.FiniteRamseyClass
#check StructuralRamsey.RelStructure.ClosureRule
#check StructuralRamsey.RelStructure.ClosureDescription
#check StructuralRamsey.RelStructure.IsUClosed
#check StructuralRamsey.RelStructure.IsUSemiClosed
#check StructuralRamsey.RelStructure.IsUSubstructure
#check StructuralRamsey.RelStructure.UClosureHull
#check StructuralRamsey.RelStructure.USize
#check StructuralRamsey.RelStructure.IsUIrreducible
```

A full `Embedding` reflects all relation tuples. Ordinary Gaifman
`Irreducible` and intrinsic U-irreducibility differ. `IsUClosed` gives
one entire output tuple over every full embedded nonempty root;
`IsUSemiClosed` permits missing but not ambiguous outputs.
`IsUSubstructure` concerns an actual subset; `UClosureHull` is a
different generated set. The small-test local cutoff counts the
original subset vertices, NOT its U-size or closure-hull size.

## The complete corrected relational theorem

```lean
import AllThoseRamseyClasses.PublicAPI
open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v
variable {L : RelLanguage.{u}}
example
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules) :
    FiniteRamseyClass K :=
  coordinated2019_ramsey_by_profile_sparsening R K rules hR hIrred hK
```

This is compiled in
[Examples/MainTheorem.lean](../../AllThoseRamseyClasses/Examples/MainTheorem.lean).
The corrected class hypothesis requires subclass membership,
finiteness, U-closedness, induced U-closed heredity, actual finite
strong amalgamation, isomorphism invariance, and the exact
local-completion implication for all original weak bounded tests.
The full compiled field-by-field blueprint is in
[Examples/ClassApplicationBlueprint.lean](../../AllThoseRamseyClasses/Examples/ClassApplicationBlueprint.lean).

## A complete nontrivial class instance: posets

```lean
import AllThoseRamseyClasses.ApplicationsAPI
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Applications.OrderedPosets

#check orderedPoset_exactLocalAtControlCard
#check orderedPoset_isCoordinated2019Multiamalgamation
#check orderedPoset_isRamsey
example : FiniteRamseyClass orderedPosetClass :=
  orderedPoset_isRamsey
```

The named language uses strict order `.lt` and reflexive poset
`.equiv`, plus an inert empty `.mate` relation. The local cutoff
is `Nat.card Y` on the ORIGINAL control C0. Its proof does not
assume the candidate weak C is ordered or the protected map globally
injective. The target conclusion has no remaining class-hypothesis
input.

For the separate finite partial-single-valued-function Ramsey theorem:

```lean
#check StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions
```

## Re-run verification

```bash
lake update
lake exe cache get
lake build
python3 scripts/audit_library.py
```

The project CI additionally builds ALL individual source files, every
`CheckAxioms*.lean` endpoint, and finite counterexample regressions.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted by the
axiom audits. Use `#print axioms` on downstream theorem endpoints and
read all implicit hypotheses before claiming a Ramsey corollary.
