# Track C: corrected-source lex-minimal initialization with actual mixed separator

16 November 2026. This branch uses only the already merged Lean modules
for the injective global lex minimizer (#1236), genuine smallest mixed
geometric separator, all-width positive B-source flip (#1226/#1240)
and finite inside/outside source counting.

Two theorem endpoints:

1. `exists_closedRange_injectiveLex_minimalMixedPiece`: in one ACTUAL
native F-forbidden source weakly EHN-mapping to the full free target,
combine injectivity, global lex (A-exclusive SOURCE, B-exclusive SOURCE)
minimality, and a smallest positive-width TRUE mixed geometric separator.
The piece is constructed from the SAME finite source/map, without a
separately postulated mixed-piece or root-injectivity hypothesis.

2. `exists_closedRange_lexMinimum_actualFlip_strictGlobalBAtradeoff`:
the checked all-width positive-rank theorem constructs a new ACTUAL
forbidden source/map with strictly smaller GLOBAL B-exclusive SOURCE
support than the original chosen lex-minimal witness. By EXACT
exterior conservation + finite inside/outside source partition,
this is a strict global decrease (not just local B rank).
Global lex-minimality forces the new TOTAL A-exclusive SOURCE count to
be STRICTLY LARGER. This is a precise structural *cost obstruction*,
not an A-neutral flip or a contradiction to the original minimum.

Critical scope and still-open gates:
- Family F must be closed under ACTUAL vertex-surjective EHN images.
  The printed tuple-surjective image closure is insufficient in general.
- Every forbidden weak EHN map into this fixed Target must have
  FUNCTION-CLOSED actual range. This is automatic in purely relational
  languages, but NOT for functional languages; the corrected hypothesis
  remains independent and explicit.
- The free amalgam sides must be individually F-EHN-free, connectedness
  of F-members and common genuine global canonical lifts remain premises.
- The original 2019 Claim 2 / unrestricted strong amalgamation is not
  established. In particular, the new B-decreasing source cannot be
  fed back into the original A-minimal geometric argument without a new
  globally sound potential or alternate surgery: it has more A support.
- No weak-image quotient, external arbitrary assumption of a geometric
  mixed piece, new Lean axiom, `sorry`, or manuscript change.
- Exact-head all-module CI, named axiom inventory, and source integrity
  must pass before merge. Keep DRAFT until verified.

Frozen numbered manuscript untouched. No collaborator-removed TODO restored.
