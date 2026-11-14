# Track B: bounded descent and full-native positive-rank trichotomy

**14 November 2026 · Draft PR #1158 · exact-head Lean CI pending**

## Concrete new Lean modules

1. `Claim2PartnerFullLocalInvariantStep.lean`: reconstruct the verified
   genuine matched-boundary inner geometric source piece and use the SAME
   actual selected-Q replacement to preserve the old ordered target-root
   injectivity and local B-active target-boundary injection. The output also
   carries the original canonical global piece symbol, exact exterior
   SOURCE-counts for all target subsets, a surviving A-exclusive SOURCE
   anchor, and strict local B-exclusive SOURCE-rank descent.
2. `Claim2NativeBActiveBoundaryBridge.lean`: turn the new target-B-boundary
   certificate into precisely the **native weak-right generated-boundary
   hypothesis** required by the next iteration, using the already checked
   target-free-amalgam equivalence
   `weakFreeRightPart_iff_fullFreeRightExclusiveTarget`. No global
   seam-injectivity assumption is introduced.
3. `Claim2PositiveRankFullInvariantDichotomy.lean`: the no-escape positive
   B-rank partner-versus-smaller-root theorem, with both root-target and
   native next-state B-boundary injections preserved in the partner case.
4. `Claim2SmallerRootFullInvariantFlip.lean`: explicitly conditional
   no-old-root-capture, no-A-mixed smaller-root genuine selected-Q
   successor with the same full native iterative invariants.
5. `Claim2PositiveRankFullStateObstructions.lean`: combine the two
   real successor cases. At positive B-SOURCE rank, return ONE actual
   new native geometric outer source carrying the complete iterative
   local invariants, **or** a genuine smaller-root component capturing
   an OLD outer-root SOURCE vertex, **or** an A-mixed smaller-root
   selected component. Both obstruction alternatives stay exposed.

## Quantitative abstract iteration

`Claim2ConditionalFiniteChain.lean` and
`Claim2ObstructionOrZeroDescent.lean` provide an exact finite-chain
interface, strict bound
`chainLength + terminalRank ≤ initialRank`, and an
obstruction-sensitive descent theorem:

> Given initialized and step-preserved validity, and a positive-rank
> step-or-(old-root-capture/A-mixed) alternative at each valid state,
> a finitely reachable valid state has either zero B-source rank or
> one of those two explicitly witnessed obstructions.

This **does not** assert that every positive-rank geometric state has a
step. Earlier `Claim2IteratedContextualDescent` and
`Claim2ReachableObstructionGate` already cover more general
terminal/obstruction reachability; the new point here is the precise
rank budget and the concrete same-source local invariant package.

## Remaining hard obligations

- Establish **initial** generated B-active boundary injectivity for the
  original source minimizer (it does not follow from ordered outer
  root-image injectivity alone).
- Handle the genuine old-root capture and A-mixedness cases; the
  trichotomy does **not** eliminate them.
- Bundle actual heterogeneous finite forbidden source states with
  fixed outer root width, original target root-coordinate vector,
  global selected symbol, exterior source-profile, A anchor, and
  root/native boundary injections. Instantiate the abstract
  finite-chain theorem with the **actual** positive-rank relation.
- Supply the original zero-B-rank terminal A-minimizer contradiction;
  terminality of B-rank descent alone is not enough.

## Audit and validation status

All newly stated hypotheses are explicit. Source counts use
`Nat.card` of literal source vertices; no image-count quotient,
unproved seam injection, second arbitrary Q, new axioms, or edits to
the frozen numbered 2019 paper. Author-removed TODOs stay removed.

New named `#print axioms` / `#check` source files and active-root
registrations were added. The new files are a **proposed Lean proof**
until an exact-head Lake/Lean build and no-admissions, axiom and
source-contract audits pass. In particular, do not mark Claim 2
or general strong AP as formally proved from this PR alone.


## 14 November follow-up: ACTUAL heterogeneous source-state instantiation

The earlier abstract step/rank model is now instantiated with the native
source geometry, not an unimplemented `Valid` or hypothetical successor:

- `Claim2HeterogeneousNativeState.lean` records a heterogeneous finite
  forbidden source `Carrier : Type`, actual geometric minimal-separator
  outer piece, original EHN map, A-exclusive source anchor, root-in-seam,
  injective ordered target-root and full native B-active generated-boundary
  injection. It constructs a real strict native state step from the verified
  positive-rank trichotomy, or returns a literal old-root-capture /
  A-mixed smaller-root witness.
- `Claim2HeterogeneousNativeDescent.lean` proves the **concrete** finite
  step chain reaches rank zero or either obstruction, with
  `steps + terminal rank ≤ initial rank`. The original *entire* global
  selected symbol, ordered target-root coordinates, exterior SOURCE
  multiplicities for every target subset, and A-anchor target value
  are transported from the initial state through the chain.
- `Claim2OriginalMinimizerObstructionReduction.lean` constructs the
  original `ForbiddenEHNWitness` from the initial geometric state
  and applies the **existing verified**
  `claim2_originalMinimizer_contradicted_by_zeroTerminalBSupport`
  at a terminal zero-rank state. Consequently, for an initial
  **globally A-source-support-minimal** witness that already carries
  the two explicit injection properties, finite actual descent must
  reach **old-root capture OR A-mixedness**. This closes the zero-rank
  branch without an unproved terminal-exit hypothesis.

### Remaining genuine Claim 2 obligations

1. The original chosen globally left-minimal forbidden EHN witness
   must be equipped with an initial geometric piece whose ordered
   root-target map and **all B-active generated boundaries** are
   injective. That is not a general property of weak maps.
2. Show that the old-root-capture and A-mixed smaller-root outcomes
   are impossible (or devise valid additional geometric moves
   decreasing a well-founded lexicographic measure while preserving
   all native state invariants).
3. Only after (1) and (2) could the full original Claim 2 and
   unrestricted strong amalgamation follow from this pathway.

The terminal theorem and minimizer comparison are reused unchanged.
All new theorems and source/axiom audit files must pass exact-head
Lean and source-contract CI before being marked verified or merged.
