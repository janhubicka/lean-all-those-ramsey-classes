# Track C: exclude width-one B-side capture under global original A-support minimality

14 November 2026. Stacked on #1184 → #1183 → #1182 → #1178.
No edit to the original 2019 numbered paper. Full exact-head
Lean and named theorem-axiom checking pending.

For a finite original F-forbidden source and EHN weak target map
chosen GLOBAL minimum in A-exclusive SOURCE support (across all
F-forbidden finite sources and maps to the fixed same target),
let P be a globally nonroot-size-minimum genuine mixed piece
whose entire closed ordered root lies in the target seam.
Take any genuine smaller positive-width minimal separator d,
whose root lies in P and the full seam, whose endpoints
d.left and d.right belong to the old P selected component,
whose d.right is A-exclusive, and whose ordered d.root maps
INJECTIVELY into the full target seam.

The previous theorem (PR #1184) shows that d's OPPOSITE
d.right component MUST contain some old P-root SOURCE vertex.
If that old P-root set is a SINGLETON, a distinct B-side
selected d.left component cannot simultaneously contain
that same old root: the two genuine components are DISJOINT.

This module formalizes:
1. exact uniqueness of the source root when n=1;
2. exclusion of any d.left capture if the old source-root
   set is intrinsically unique;
3. specialization to old P.width=1.

Thus under original global A-minimality and global smallest
mixed-piece minimality the width-one captured B-side alternative
is impossible. There is no extra whole-seam injectivity:
only d's actual ordered target-root images are required
injective, as provided by the merged smaller-root certificate.

The n>1 split-capture pattern with different old-root vertices
in d.left and d.right remains open. This also does not
establish the original zero-B-rank terminal contradiction
or recover arbitrary initial normalization.

Three named #print axioms checks and protected active root.
No removed collaborator TODO has been reinstated.
