# Track B — global selected symbols imply width and all-test profile

**12 November 2026.** Original 2019 manuscript remains frozen.

## Narrow mathematical result

The merged fixed-width theorem `geometricGlobalPieceSymbol_eq_iff_fullRoot_allTests`
states that, at a prescribed positive root width, equality of the
original global selected symbol is exactly equality of the full native
root structures and of all forbidden-rooted full diagram tests.

We now make the width an *output*, not an independent input.
`selectedFunctionalChart_globalSymbol_eq_iff_width_root_allTests`
compares actual selected charts at arbitrary positive widths `n,m`.
Equality of their dependent original global symbols forces an equality
`n=m`; after explicitly transporting the second selected chart along
that equality, the entire functional root and all forbidden native
diagram tests agree. The converse follows from the fixed-width theorem.
No arbitrary unselected charts are admitted.

`geometricGlobalPieceSymbol_eq_iff_width_root_allTests`
specializes this to two arbitrary genuine finite forbidden geometric
source pieces, without assuming their positive widths already coincide.
The result is suitable for a future Claim 2 state invariant retaining
only the original global selected symbol, instead of independently
storing the root width, full root structure, and full test profile.

## Explicit nonclaims

The new result does NOT prove that an outer-root tuple has an injective
image in a weak EHN target map. It does not establish an eligible inner
B-only successor at positive local B-rank, a terminal left-minimizer
contradiction, or the unrestricted original Section 3 theorem.
It is *source-side* information with an explicit dependent transport.

## Validation gate

Do not promote the new theorem until the **exact head** has passed:
full Lake project build, named `#print axioms`, permitted-axiom inventory,
active-root/integrity audit, Section 3 contract audit, and no-admission
scan. Keep the PR draft until these gates complete.

The existing fixed-width theorem and concrete same-selected-Q proof
from merged PRs #985/#997 are unchanged.
