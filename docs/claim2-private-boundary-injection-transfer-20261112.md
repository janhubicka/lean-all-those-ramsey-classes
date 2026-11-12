# Track C — exact active source-boundary injection across two full source replacements

**12 November 2026. Draft requiring exact-head Lean CI.**

The verified full-native `fullFreeAmalgam_replacement_privateBoundary_pair`
says that for two independently chosen glued full functional sources
Old = Qold +_Root E and New = Qnew +_Root E, a private E-component
after deleting a root-containing subset SR of E has its COMPLETE
function-generated boundary carried by the same retained
`T_E = Cl_E(N_E(component_E(SR,x)))`:

  OldBoundary = iOldE '' T_E,
  NewBoundary = iNewE '' T_E.

The new theorem
`fullNativeReplacement_privateGeneratedBoundary_injection_transfer`
assumes only:
1. both full native source diagrams are actual free amalgams;
2. the old/new weak target maps agree on every retained E source
   vertex, not just a selected root tuple;
3. the OLD target map is injective **on the old private generated
   boundary**, not on the entire old common-seam preimage.

It derives that the NEW target map is injective on the
corresponding NEW generated boundary, even if some Q-nonroot
vertices elsewhere collide with the common target root.
No forbidden-family minimizer, source-image quotient, global
target injection or distinct-image rank is assumed.

This is an exact two-step support lemma for a prospective
**B-active generated-boundary invariant**. It does not itself
identify the target-seam B-only component with the particular
private E component: that requires a source path-transport
lemma respecting the seam deleted set in BOTH actual source
diagrams. It also does not handle smaller-root seam-incursion
cases where the selected component becomes mixed.

The numbered 2019 manuscript remains frozen; no previously
removed TODO is reintroduced. All claims await full exact-head
Lean compilation, protected-root, named-axiom and admission scans.
