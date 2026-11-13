# Track B/D: exact decomposition of the full target-seam obstruction

**12 November 2026.** New draft stacked on PR #1094.
No change to the original 2019 manuscript.

## Problem identified by the adversarial audit

The older aligned-root theorem #1087 gives an iff between
new seam injectivity and Q root reflection only when the
entire source Q-root can be matched to the entire target
common root by full embeddings. That identification is
not automatic in the original weak EHN proof.

Let `Seam` be the arbitrary full TARGET common seam, and

```lean
S_Q := Set.range (fun r : R => flip (iNewQ (qRoot r)))
```

the image of the ACTUAL selected source root. We assume
`S_Q ⊆ Seam` as an explicit exact root-coordinate
premise, not that these sets are equal.

## New decomposition theorem

`fullNativeReplacement_fullSeamInj_iff_QrootReflection_and_residualInj`
takes a genuine full native source free amalgam `New=Q +_Root E`
and assumes the old weak source map f is injective ONLY
on old retained-complement source vertices mapped into S_Q.
The weak new map agrees with the old map on ALL of E.

It proves the exact equivalence:

* new flip is injective on the entire preimage of Seam;
* **both**:
  (i) Q reflects the smaller actual root image S_Q,
      meaning all Q source vertices mapped into S_Q
      lie in the actual source Q-root; and
  (ii) flip is injective on the preimage of Seam \ S_Q.

The proof splits collision pairs according to whether
their common target image lies inside or outside S_Q.
On S_Q it reuses the iff from parent PR #1094.
Outside S_Q it retains the explicit residual
injectivity obligation. No full target-root alignment,
source carrier finite cardinality or forbidden-family
closure assumption is introduced.

## Precise remaining mathematical obligations

This does NOT prove either (i) or (ii) for the original
selected-Q canonical replacement. It demonstrates exactly
how the general seam-collision question separates:

1. Q-nonroot collapsing onto a genuine SOURCE-root image.
2. Weak target collisions at additional target common-root
   values outside the actual SOURCE-root-image S_Q.

A smaller-root geometric alternative from Claim 2 is
still separate and is NOT a numerical `m < n`
rank decrease without a further theorem.

The source-side equal-global-symbol invariant from merged
Track B does not solve (i) or (ii), since it concerns full
native source charts, not weak TARGET-image collisions.

## Verification

Draft until parent #1094 is exact-head verified/merged,
then retarget to main and pass its own full project
Lean build, named `#print axioms`, permitted-axiom,
source-integrity, active-root and no-admission audits.
