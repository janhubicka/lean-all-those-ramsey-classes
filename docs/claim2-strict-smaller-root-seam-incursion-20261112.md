# Track C: strict smaller generated opposite root necessarily incurs into seam

**12 November 2026. Independent source-geometric Lean draft; CI unverified.**

Let T be any full-native function-closed source cut separating x,y,
and suppose it is the **entire function-closure of the external
neighbourhood** of the x-component after deleting T.
Set U to the **entire function-generated external neighbourhood**
of the opposite y-component after deleting T. The checked
`oppositeBoundaryClosure_isMinimalClosedSeparator` proves that
U is itself a minimal closed separator of x,y, with U ⊆ T.

**New proposed theorem**:
`strictOppositeGeneratedBoundary_forces_xSideSeamIncursion`.

If U ⊊ T, there is a literal SOURCE vertex z in T\\U which
belongs to the component of x in Source minus U. The argument:

1. The original component C_T(x) embeds in C_U(x), since U⊆T.
2. If C_U(x) avoids all of T, then every U-avoiding edge along
   a path from x can be transported back into the T-avoiding
   component C_T(x), so C_U(x)⊆C_T(x).
3. Equality of these two source components makes their exact
   generated external boundaries equal. But minimal closed
   separation at U implies the new x-side boundary is U,
   whereas the original x-side boundary is T. Thus U=T,
   contradiction.

This argument requires neither finite source, forbidden-family
membership, A-support minimizing witnesses, common lift, nor
weak-map injectivity. It is valid in the native complete
set-valued functional language and includes nullary functions.

## Consequence for positive-B-rank Claim 2 selection

In the smaller-root alternative of #1015/#1020, T is a subset
of the original complete seam preimage S. Hence the strict
root shrink necessarily introduces at least one S vertex
into the B-originating x-side component (after deleting U).
The alternative is therefore **intrinsically seam-mixed**,
which identifies precisely why it cannot be treated as an
ordinary B-only inner geometric piece. This strengthens the
obstruction diagnosis, but does **not** prove an admissible
positive-rank flip or root-collision elimination.

Still needed: an alternative state/rank treatment of the seam
incursion, or a separate argument ruling out the smaller-root
alternative for the concrete forbidden source. Keep the
2019 numbered manuscript frozen; do not reinsert removed TODOs.
