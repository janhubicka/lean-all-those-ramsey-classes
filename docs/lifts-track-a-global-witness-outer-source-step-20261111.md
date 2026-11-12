# Track A: actual nested outer source symbol from one inner global witness

**11 November 2026. Verified original interface; 12 November extension proposed.** The original 2019 numbered manuscript is frozen;
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

Original #1006 merged after exact-head CI. Hold the 12 November strengthening
in draft until its own exact-head pinned full Lean, permitted-axioms,
source-contract/import, no-admissions and active-root checks succeed.
The named axiom endpoint is
`CheckAxiomsNestedGlobalWitnessOuterSourceFlip.lean`.

## 12 November: stronger same-witness exterior invariant (new draft)

The new `nestedGeometric_actualGlobalWitness_restores_outerSourceSymbol_withExterior`
retains the **same** selected Q, literal new forbidden source, complete
free-amalgam maps, original ordered outer roots and **exact outer carrier**
in one certificate. It also proves, for every target subset `TargetSet`,
the equality of cardinalities of SOURCE vertices outside the actual
old/new outer geometric pieces mapping into `TargetSet`.

This strengthens the merged #1006 source-symbol theorem without new
hypotheses. The historical exported theorem remains a direct projection
and preserves its exact signature. The new cardinality statement follows
from the already verified `geometricFlip_actualOuterExterior_sourceSupport_card_eq`
once the exact carrier and unchanged complement agreement are retained
from the SAME replacement witness.

This is not the strict internal B-rank decrease. In particular it does
not choose an eligible positive-rank inner flip or establish printed
Claim 2; it supplies the exterior SOURCE-count invariant *conditional*
on the given inner global witness and actual nested source geometry.
No outer target-root image injectivity is assumed.
