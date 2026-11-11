# Track A: actual nested outer source symbol from one inner global witness

**11 November 2026. Draft audit.** The original 2019 numbered manuscript is frozen;
no previously removed collaborator TODO is restored.

## Conditional theorem

`nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol` takes an
actual finite forbidden full-functional source `Old`, genuine inner and outer
geometric pieces with the inner selected component nested in the outer,
positive inner/outer widths, a weak EHN map `f:Old→Target`, and a REAL
inner canonical global relation in a second witness `B` with exact
coordinates `jB(xsB i) = f(inner.roots i)`.

It constructs a finite forbidden native full source `New`, a weak EHN
map `flip:New→Target` and a **genuine** new outer geometric piece such that
its **original globally indexed** canonical piece symbol equals the old
outer source symbol and the images of all ordered outer root coordinates
are unchanged.

The proof does not posit arbitrary Q/free amalgams: it extracts one
genuinely selected Q via the verified original-global witness theorem,
uses the fixed-root equivalence of canonical gluing diagrams, then
applies the verified exact-carrier nested geometric reconstruction to
the **same** Q and `New`. No second replacement is chosen.

## Critical nonclaims

- The output is equality of source **symbols**, not a target relation at
  a non-injective outer tuple. An outer image collision is permitted
  here. Track D still owns that obstruction.
- The inner global relation is an **assumption**, and it already implies
  that the inner root images are distinct, since global relations are
  injective tuples and `jB` is an embedding. This is not a general
  collision-tolerant existence result.
- No positive-rank eligible inner piece is constructed from an arbitrary
  Claim 2 state, and no terminal A-minimality contradiction follows;
  those remain Track C. No global strong AP is concluded.

## CI acceptance

Hold draft until exact-head pinned full Lean, permitted-axioms,
source-contract/import, no-admissions and active-root checks succeed.
The named axiom endpoint is
`CheckAxiomsNestedGlobalWitnessOuterSourceFlip.lean`.
