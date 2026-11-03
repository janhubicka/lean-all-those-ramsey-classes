# Adversarial audit and import-closure cleanup — 3 November 2026

## Scope and verified baseline

Repository: `janhubicka/lean-all-those-ramsey-classes`, main baseline
`bdaf69dd19fbe168afe0a99082f4f760899263ef`. The completed main-branch
Lean workflow [41560191346](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/41560191346)
passed its all-module build, source/inventory checks and axiom certificates.
A prior cancelled run at the same head must not be mistaken for a failure.

This review rechecked the curated `PublicAPI`/`ApplicationsAPI` distinction,
the certified corrected relational main theorem's proof route, the conditional
original functional strong-amalgamation contract, the active-root inventory,
and the two source-audit scripts. It does **not** claim a new manual line-by-line
refereeing of every upstream theorem or a fresh proof of the native lifting
section.

## Adversarial findings

1. The corrected RELATIONAL 2019 theorem is unconditional relative to its
   **revised** multiamalgamation-class hypotheses. Its constructed sparse
   witness is used by `coordinated2019_theorem218`; no missing rank-increment
   constructor is an additional premise. This does not prove the printed
   native generating-rank lemma or remove the need for a relationalization
   interface when making a primitive-function claim.
2. `Lifts/GlobalMaximalTraceConditionalStrongAmalgamation.lean` explicitly
   assumes `hFreeK : GlobalCanonicalShadowFreeAmalgamation F K`. This is
   an additional hypothesis rather than a consequence of regularity and
   native strong amalgamation. The entire original Section 3 theorem cannot
   be certified by invoking that conditional result. Existing source-contract
   and axiom checks correctly retain this distinction.
3. `OriginalClaim2InputCoveredOneStep` still requires image closure and
   coverage by irreducible function-input tests. For general arity, an EHN
   weak image need not be function-closed. The original Claim 2 also needs
   a genuinely geometric new outer piece with complete generated boundary,
   an iterated support decrease that interacts with left minimality, and
   resolution of root-image collisions. Preserve these as open obligations.
4. The prior retirement scanner read raw `.lean` text. An `import` inside
   a nested block or line comment could therefore create a *phantom*
   dependency, falsely keeping unused modules. The import DAG audit already
   had a comment/string masker, but maintained separate parsing logic.
   Both scripts now share that masker and recognise multiple modules per
   `import` directive. Unsupported import syntax fails closed.
5. A separately protected root marker is unnecessary if its Lean module
   is imported by another retained protected root. The cleanup removes
   selected directly/transitively redundant markers but **does not delete**
   their Lean source, proof certificates, or mathematical statements.
   All source modules remain individual Lean build targets.

## Changes and safeguards

- Extracted the existing nested-comment/string scanner to
  `scripts/lean_source.py`, removing duplication in audit and inventory
  code.
- Added tests for nested comments, line comments, strings, escaped quotes,
  multi-module imports, unclosed syntax and unsupported directives, and
  made the inventory CI job run them.
- Pruned redundant `scripts/active_roots/*.txt` entries **only** with a
  concrete surviving protected import chain, leaving supported APIs and
  live development branches untouched.
- The numbered manuscript is unchanged. This audit note preserves the
  distinction between mathematical proof obligations and infrastructure.

## Remaining mathematical obligations

To complete the original native lift, construct the outer generated boundary
after the actual selected inner replacement; transfer the entire fixed-root
incompatibility profile and original global piece index; prove terminating
local B-source support descent with the correct left-minimality contradiction;
and establish the unrestricted original shadow-avoidance lemma without
assuming injectivity or unsupported image closure. Independently distinguish
completed finite-age Fraïssé schedulers from a constructed infinite limit.
Do not promote any conditional theorem to the unrestricted printed result
without checking its complete type and axiom dependencies.

## Verification required on the cleanup branch

Run `python3 -m unittest discover -s scripts -p 'test_lean_source.py'`,
`python3 scripts/cleanup_inventory.py --verify`,
`python3 scripts/audit_library.py`, the entire `lake build`, every
`CheckAxioms*.lean` certificate, and the Section 3 contract audit.
A successful CI run on the exact cleanup head is required before merge.
