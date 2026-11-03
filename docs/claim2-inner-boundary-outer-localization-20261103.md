# Track C: source-boundary localization without intermediate A-minimality

The original Claim 2 proof uses left-support minimality to obtain the initial smallest mixed piece, but this property does **not** survive a B→A flip. A concrete new source-geometric fact, independent of ANY support minimality, is checked in `Claim2InnerBoundaryOuterLocalization.lean` (subject to exact-head CI):

Let `P = R ∪ C` be a genuine native geometric piece, `S` an arbitrary function-closed cut with `R ⊆ S`, and `x ∈ C \ S`. Then its genuine `S`-component `B = component(Source \ S,x)` satisfies
```
B ⊆ C,
Cl(N(B)) ⊆ S ∩ P.
```
In fact the first boundary conclusion holds for ANY subset `B ⊆ C` after dropping the factor `S`.

The proof uses only source Gaifman path containment and the closedness of the original geometric `R ∪ C` under **all native partial/set-valued functions**. It does not assume an EHN weak map is injective, a root is singleton, either old/new root is comparable, the source is left-minimal, or `Cl(N(B))` is a minimal separator.

This discharges the FULL inner-boundary containment obligation for a B-only `S`-component lying inside an outer piece, even in an intermediate forbidden source.

### Not yet proved

Containment of the generated root in the outer piece does **not** imply that the root is an inclusion-minimal closed separator with an opposite boundary partner. The universal positive-B-rank successor requires that partner (or a valid alternative), target-root injectivity, and proof that the same canonical replacement remains a genuine geometric outer piece with complete profile and exact exterior. These are still the real mathematical obstacles, not consequences of this localization lemma.

No frozen manuscript prose changed. A separate axiom audit and active proof root are registered. Keep Claim 2 only partially validated.
