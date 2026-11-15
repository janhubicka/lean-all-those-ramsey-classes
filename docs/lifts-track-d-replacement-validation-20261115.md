# Track D: replacement argument and Ramsey-contract validation

## Exact source snapshot and scope

The audit started at PR #1247 head b1dfd4eee5aae5a72dc9f333184b70cf37ea291c, stacked on PR #1228 head 074a6d670ebca469960a0623981f3b0cf3654440. The old sparse-control hypothesis has already been corrected there to require IsFiniteNamedMaximalTrace Family Bbar; its marked-witness proof uses the SAME hBar certificate. The previous all-Bbar quantifier was mathematically impossible whenever the named family has a forbidden member.

## Mathematical verdict on the replacement

Let G=FullRangeEHNSaturation F. G consists of complete target structures of vertex-surjective EHN maps from finite original forbidden sources; extra target incidences are retained. EHN composition proves image closure and Forb_EHN(G)=Forb_EHN(F). In a relational language the actual full induced target range H of f:S->D is automatically a closed substructure, and S->H is surjective EHN. Hence H belongs to G and its inclusion into D is a full embedding.

For any target subset U, the original support subtype {s : f(s) in U} SURJECTS onto {h in range(f) : h in U}. Thus full-image replacement cannot increase the finite source-support count. Starting from a genuine global support minimum over G makes the replacement a minimum as well. No initial injectivity, root-injectivity, tuple-surjectivity onto the full image, or arbitrary functional range-closure premise has been smuggled in.

The existing Claim 1 source flip applies to this FULL-embedding minimizer, with G in every occurrence of family membership, canonical-lift indexing and minimization. It does NOT apply merely from agreement of the original F-lifts. The finite-signature/uniform-source-bound representative cover is legitimate but is not needed for normalization itself. The entire general functional and infinite-regular-family theorem remains a separate claim.

## Corrected sparse-control contract: exact strength

The new source theorem boundedSaturationFolded_sparseControls_iff_orderedRamsey proves a converse to the marked-witness reduction. A genuine finite age Ramsey target supplies a sparse control by using itself and literal weak inclusions into its own forbidden-free shadow. Together with the existing forward reduction this is an EQUIVALENCE with the precise ordered Ramsey conclusion currently written.

Therefore correcting the admissibility quantifier removes a false premise, but DOES NOT independently solve or weaken the missing nonempty-family Ramsey construction. Do not count this conditional equivalence as an unconditional Ramsey theorem or treat the ambient full-language Ramsey theorem as producing forbidden-free controls.

Two consistency checks accompany the equivalence: any admissible right pattern is its own one-colour control, and the empty original forbidden family has all finite-colour controls via the existing ambient ordered Ramsey theorem. These distinguish a valid, unproved general contract from the former inconsistent one.

## Independent executable finite audit

A separate Python checker tests ALL structures on at most two vertices in a unary-plus-symmetric-binary language with loops, and ALL loopless structures on three vertices: 101 models and 151029 maps. It checks positive relation preservation AND full reflection on every irreducible induced source test, including singleton unary values and loops.

PASS: 5815 genuine EHN maps; 5815 full induced-range EHN factorizations; 5815 full range inclusions; 44797 source-support inequalities over every tested target subset; 1453 EHN composition checks; 273 surjective-composition checks; 30 exclusions of the forbidden right-pattern control; 2 loop-caveat tests; 8 two-colour positive control tests for a nonempty marked-singleton forbidden family. These are bounded computational checks, NOT a proof for all structures or a Lean kernel certificate.

The independent saturation nonregularity checker also passed: all 379 deletion sets of size <3 in the 27-vertex blowup, all 18473 deletion sets of size <4 in the 48-vertex blowup, and both unmarked and marked-root-reflecting odd-walk thresholds for indices 3 through 6. The infinite graph construction still needs its native Lean bridge.

## Kernel status and remaining gates

This runtime has no Lean, Lake or Elan installation and outbound GitHub DNS resolution failed. No local Lean compilation was claimed. The GitHub exact-head jobs were still queued at audit start. New source theorems have named axiom checks and an active-root registration; their Lean status remains UNVERIFIED until the exact-head all-module build, axiom audit, source contracts and inventory pass.

The mathematical audit of the relational replacement is complete at the stated conditional scope. The full native maximal-lift counterexample bridge, general Claim 2 iteration, nonempty-family Ramsey-control construction and fresh exact-head kernel certification are NOT complete. Frozen numbered manuscript untouched.
