# Track C — actual finite global A-minimal and lexicographic (A,B)-minimal source witnesses

15 November 2026. Standalone additional Lean module from merged
main. Exact-head CI/axiom/admission/integrity/root-inventory pending.
Original published 2019 manuscript remains frozen.

This addresses one exact INITIAL MINIMIZATION obligation often
left as a free hypothesis in the Claim 2 continuation.

Suppose there exists ANY finite original F-forbidden native
source Old with true weak EHN map f to the fixed target full
amalgam. Assume every member of F is finite (hFiniteF).
Given a fixed target set Active, consider the subset of
natural numbers consisting of total Active SOURCE counts
of ALL forbidden-source / weak-map witnesses to this SAME
fixed target. It is nonempty. Nat.sInf_mem produces one
actual witness attaining the minimum, not an abstract
unattained infimum or minimum of distinct TARGET images.

`exists_global_minimum_weakForbiddenSource_support`
returns an actual F-forbidden finite native source and weak EHN
map with global minimality inequality for all candidate witnesses,
including those with different source carrier types.

`exists_global_lex_minimum_weakForbiddenSource_support`
first selects the global minimum of A-exclusive genuine source
support. Among ALL eligible witnesses attaining EXACTLY that
A-cardinality, it then chooses the least B-exclusive genuine
source support, again via Nat.sInf_mem. The output is ONE
forbidden source/weak map globally minimum in A and B-minimum
among those tied on A. Weak maps are never assumed injective.

This is only a witness MINIMIZATION theorem. It does not
supply an actual globally minimum A/B-mixed geometric piece
inside the selected witness; the existence and selection of
such a mixed piece remain separate. It does not imply an
actual selected Q preserving the A-minimality class, and
so it does not complete the positive-B-rank induction or
the terminal 2019 contradiction. The quantitative issue
is precisely characterized in draft #1196/#1206/#1207/#1208.

No target-image quotient, unproved tuple-surjective weak
source-image reduction, or reintroduced collaborator TODOs.
Two named #print axioms and protected active source root.
