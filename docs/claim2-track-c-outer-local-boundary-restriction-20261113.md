# Track C: no extra injectivity needed on the old retained source

**13 November 2026. Standalone conditional Lean helper; exact-head CI pending.**

The already kernel-validated local B-boundary dichotomy #1106 requires
that the weak map be injective on every entire generated boundary
of B-exclusive source components based at vertices within the
current actual geometric outer piece P.

The piece-scoped source replacement theorem proposed in #1123 uses
the same property for retained old complement E vertices only.
This is not an additional assumption. Each retained e is a
literal old source vertex iOldE(e) in P; B-exclusive target
membership and complement of the target common seam give the
corresponding B-source component basepoint. The generated
boundary is the very same source subset.

The theorem
`claim2_outerBActiveBoundaryInjection_restrict_to_retainedComplement`
performs the exact source/target predicate conversion with no
source-image quotient and no extra injectivity.

This is a low-level interface lemma: it neither derives initial
local B-boundary injection from arbitrary EHN maps nor supplies
the mixed-smaller-root source selector or zero-B-rank exit.
Its intended use is on the SAME old/new selected-Q source witness
as in the conditional strengthened full-native source APIs
#1117 and #1120 and piece-scoped transfer #1123. Avoid choosing
two independent existential replacement sources.

No change to the numbered manuscript or collaborator-removed TODOs.
Keep the PR draft until full exact-head Lean build, axiom,
literal admission and protected-root inventory all pass.
