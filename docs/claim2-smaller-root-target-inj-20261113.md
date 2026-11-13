# Track B/C: TARGET injectivity of a smaller geometric root

**13 November 2026.** Additive proof-strengthening only; no changes
to frozen 2019 source or collaborator-removed TODO notes.

## Mathematical statement

The already verified two-way positive-B-rank theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_of_activeBoundaryInjective`
assumes injection of the weak target map on the complete
function-generated boundary of every B-exclusive component
inside the current selected outer piece.

On its *smaller-root* alternative, the returned actual geometric
separator piece `d : GeometricFunctionalPieceData Source m`
has `Set.range d.roots ⊂ T`, where `T` is exactly the selected
B-component generated boundary. The chosen component belongs to
the old outer piece and is B-exclusive, so the assumed active-boundary
injectivity applies to `T`.

The additive theorem
`claim2_positiveRank_actualSuccessor_or_smallerRoot_withTargetRootInj_of_activeBoundaryInjective`
preserves the entire successful flip branch and original smaller-root
certificate, adding only:

```lean
Function.Injective (fun i : Fin m => f (d.roots i))
```

to the smaller-root witness.

Proof: transport the active-boundary injectivity along the exact
boundary identity; restrict it to the smaller-root image using
`Set.range d.roots ⊂ T`; compose with the *actual*
`d.roots_injective`. Thus full weak seam injection is not used.

## Nonclaims and next open problem

The smaller-root piece can still be MIXED; no valid B-to-A
same-symbol successor exists by this certificate alone.
Its arity `m` is not known to be less than the original root
width `n`: set-theoretic containment in a generated boundary
is insufficient for such a claim. No proof of full common-lift
compatibility, terminal contradiction, or unrestricted strong AP.

What this DOES exclude is an additional target-coordinate
collision *on the smaller root tuple itself*. It is safe to
use that tuple as a genuine injective ordered image in a
subsequent canonical-relation/compatibility argument.

## Validation

Draft until exact-head full Lean project build, named
`#print axioms`, source integrity, active-root,
permitted-axiom inventory, Section 3 contract audit
and no-admission scan pass. The existing two-way theorem
and all of its code remain unchanged.
