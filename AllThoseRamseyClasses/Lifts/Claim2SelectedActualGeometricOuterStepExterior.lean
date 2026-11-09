import AllThoseRamseyClasses.Lifts.Claim2SelectedActualGeometricOuterStep

/-!
# Backwards-compatible import: same-Q exterior support invariant

The strengthened one-step proof
`geometricGlobalRightFlip_actualOuterPiece_strictLocalRightSupport_withExterior`
now lives in `Claim2SelectedActualGeometricOuterStep`, which also defines
the original strict-local-rank theorem as a direct corollary. This
historical module remains an import alias so downstream Lean files
using the old module path continue to compile.

Source geometry and exterior support are still conditional on an
eligible B-only selected inner flip. This consolidation neither
discharges Track C's positive-rank selection/terminal contradiction
nor resolves Track D's weak-image root collision.
-/
