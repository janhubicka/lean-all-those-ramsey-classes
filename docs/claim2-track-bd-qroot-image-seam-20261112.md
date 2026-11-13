# Track B/D: source-Q-root-image seam criterion

**12 November 2026 — new conditional source theorem.**
The original 2019 manuscript is frozen.

## Source root image versus the full target common seam

The previously verified and merged aligned-root iff theorem (#1087)
identifies the SOURCE root and the entire target common root
via a full embedding and matching coordinates.

The general original Claim 2 situation need not satisfy that.
In general, let

```lean
S_Q := Set.range (fun r : R => flip (iNewQ (qRoot r)))
```

be the target image of the actual SOURCE Q-root tuple.
There is **no assumption that S_Q equals the entire target
common seam**, or even that a full target-root embedding of
the same structure R exists.

## New verified-target interfaces

1. `fullNativeReplacement_newComplement_seamInjective_of_local`
   upgrades the pairwise source-complement statement from
   #1083 to the precise `Set.InjOn` invariant on the entire
   new retained complement image intersected with any target
   Seam. It assumes only old complement-local seam injection
   and literal target-map agreement on ALL retained vertices.
   There is no claim that Q-exclusive new vertices are injective.

2. `fullNativeReplacement_newQrootImageSeamInj_implies_QrootReflection`
   observes that any Q vertex mapping into S_Q has the same
   target image as some actual Q-root vertex, by definition
   of S_Q. Thus new seam injection forces it to be that root
   vertex, by injectivity of the full source Q embedding.
   This direction needs NO old injection, free-amalgam or
   target-root embedding.

3. `fullNativeReplacement_newQrootImageSeamInj_iff_QrootReflection`
   combines that direction with the merged #1083 sufficient
   converse under only old retained-complement-local
   injectivity on the preimage of S_Q. It states an exact
   iff between full new map injection on S_Q and reflection
   of S_Q by the Q-side map, for any native full free
   amalgam New = Q +_Root E.

## Critical limitation

The target common seam X in printed Claim 2 can be
STRICTLY BIGGER than S_Q. New source vertices can map
into X but outside S_Q, without colliding with the
Q-root. Therefore this iff does not prove new injection
on the FULL common seam, nor eliminate nonroot-to-X
Q-side defects beyond the smaller Q-root image.

No target-image quotient is formed. No root-width
measure decrease, forbidden-family image closure,
positive-rank successor existence, or original
A-support minimizer contradiction is inferred.

## Exact-head gate

Keep the PR draft until a full project Lake/Lean build,
three named `#print axioms`, permitted-axioms inventory,
active-root/source/Section-3 contract scans, and the
no-admission check all succeed. No 2019 TeX edits.
