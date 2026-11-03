# Track E alternative: profiled relational two-pass sparsening

**Adversarial construction audit, 3 November 2026.**
**Scope:** finite named all-closed-component folded maximal induced traces.
This is an ALTERNATIVE to the printed Section 3 regular infinite-family
distinct-root lift and does not validate the original Claim 2. The numbered
`ramsey.tex` remains frozen.

## Critical distinction: the direct native strict-tree increment is not a prerequisite

The direct functional partite proof in
`PartiteConstruction/Functional/NativeIteratedOriginalPartialAll.lean`
supplies a full native Ramsey arrow, an original-2019 partial
homomorphism-embedding projection, and **strict relational
function-GRAPH tree** completions for bounded weak tests. It does NOT
produce **strict FULL-function trees**. The conversion is false for
arbitrary clipped weak function graphs: a two-edge unary function
path may be a relational graph tree but cannot embed in any strict
full functional tree of the one-edge function base. The
`NativePower*` C5/C7 obstructions further warn against attempting
a generic mixed attachment rank increment at native full-function
level without extra hypotheses.

The verified *corrected* 2019 proof takes a different route:
`AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean`
(`coordinated2019_profile_sparse_witness_with_B_coverage`):

1. Apply unrestricted induced **closed** relational Ramsey construction
   to the original control and preserve its ordered arrow.
2. Adjoin **generated closure-profile** relations over the chosen finite
   Base, making its canonical profile expansion hereditarily irreducible.
   A profile on an exact enumeration records the corresponding closed
   Base hull; this adds relation information, NOT extra vertices to the
   weak test.
3. Apply the already verified **relational strict B-tree** sparsening
   theorem through the preselected exact n-vertex cutoff.
4. Complete the profiled strict trees by a **common closed K-boundary**
   extracted from the matching profile; use genuine finite strong AP.
   The root can be a nonclosed weak subset in the intermediate picture:
   the profile produces a full closed target boundary only for the
   completion, without changing the source test carrier.
5. Apply a second **closed** induced Ramsey pass in the profile-root-tag
   language to recover original U-closedness while retaining the arrow
   and the exact-image test size budget.
6. Transfer local K completions through the exact vertex image of each
   weak test. Its cardinality is <= the original vertex cardinality.
   Finish with the corrected locally finite K premise, if applicable.

The formal theorem above assumes a relational K with U-closed
heredity, finite strong AP, and actual irreducible members.
It builds the sparse picture without a native rank-increment axiom.
It does not by itself claim Ramsey for arbitrary genuinely functional K.

## Specific Track E crosswalk and remaining checks

For fixed ordered finite maximal-trace age members A*, B*:

- **Certified** #768/#770/#773/#820: choose one enlarged Bbar
  *in the actual age*, with an ordered marked B* and a single full
  native maximizing witness W_B plus exact tag profile (all truth
  values). This is the Base that must be carried through the
  relational profiling and final decoding.
- **Certified** #743/#764/#779: unconditional ordered ambient Ramsey
  control in the full extra-tag language, and the exact marked-copy
  Ramsey endgame once a sparse control's **native shadow** avoids
  the finite forbidden family.
- **Certified** #769/#772/#784: one finite family-specified cutoff
  n = total cardinality of named forbidden-source carriers, with
  native avoidance equivalent to finite forbidden-free
  **ambient-relative** completions of all literal native weak
  vertex sets S of size <= n. An ordinary EHN completion of the
  clipped weak structure is too strong (closed experimental #760).
- **Certified** #803/#806/#808: ambient-relative local completions
  pull back under full native embeddings and noninjective EHN
  projections, and expanded EHN projections descend faithfully
  through removal of extra component tags. This is the small-image
  half of the eventual profile transfer.
- **Certified** #774: copywise completion of **strict full-function**
  trees of an irreducible Base using the age's actual expanded
  strong AP. This is useful after an appropriate strict target
  has been constructed, not a license to decode an arbitrary
  weak function-graph tree into a full-function tree.
- **Pending** #813: the fully ordered Base is irreducible in the
  order-added genuine functional language. Using the relational
  function-graph irreducibility theorem avoids the old brittle
  coordinate-by-coordinate tuple proof.
- **Pending** #835 and future order-amalgamation theorem:
  transport unordered strong AP to compatible finite external
  orders by sorting target vertices according to common-root cut
  rank. The full lexicographic construction is in
  `docs/lifts-track-e-ordered-strong-ap-20261103.md`.

### Genuine remaining bridge B1: faithful encoding/decoding

The verified coordinated sparse witness is **relational**, with
full ordinary relational embeddings of complete-mask profiles.
Track E's objects are actual `Structure`s whose function fibres are
sets and where empty means undefined; they are NOT automatically
instances of the richer `PartialSetStructure` representation.
Create a faithful bridge:

  native A.func F xs = ∅   <->  Option.none
  native A.func F xs ≠ ∅   <->  Option.some (A.func F xs)

A full native embedding must give a FULL partial-set embedding,
reflecting the input domain and all output values. The decoder
must recover the original old relations, all old function fibres,
the external order, and every additional folded tag. Do NOT permit
a defined-empty Option.some ∅ input to arise unnoticed: it would
not have a faithful native representation.

Initial Lean proof candidate: `NativeNonemptyPartialBridge.lean`
(PR #846, full CI pending). Later work must show exact weak test
compatibility and return through the complete-mask relational code.
The existing `WholeMaskWeakRelativeCompletionObstruction2019`
demonstrates that a FULL embedding of an *intrinsic weak partial
restriction* does not automatically imply the ambient-relative
OLD mask homomorphism required by the 2019 profile route.

### Genuine remaining bridge B2: relational closure and strong AP contracts

Prove the chosen canonical relational encoding of a finite
maximal-trace member is U-closed under exact function closures.
Full native embeddings must correspond to the required U-closed
relational embeddings; plain function-graph induced embeddings
alone do not reflect external target function outputs. The
relational class K must be closed-U-hereditary, have finite
strong AP, and have irreducible ordered members; the ordinary
finite-family maximal-trace strong AP cannot be fed to the
relational theorem without checking that the encoding preserves
the **full overlap** and complete output profiles.

The 2019 `coordinated2019_profile_sparse_witness_with_B_coverage`
requires `K E -> E.Irreducible`: the extra external total order
will provide this once the graph encoding and ordered strong AP
are independently certified.

### Genuine remaining bridge B3: local target-to-native transfer

From a strict profiled RELATIONAL tree completion
`HasInducedClosedUKCompletion K rules (Qold.induce S)`, construct
a finite actual native forbidden-free maximal-trace target and
an `IsAmbientRelativeWeakHE nativeC S nativeTarget map`
on the **literal exact** native S. This means:
- preserve positive old relation and all surviving function outputs;
- for a nonempty ambient function fibre wholly contained in S,
  preserve the complete image-set equality, not just incidences;
- protect all genuine full ambient irreducible native tests whose
  image lies within S, not spurious irreducibles formed by clipping
  fibres;
- ensure all folded component predicates and the final marked
  Bbar-copies are reflected as FULL functional embeddings.

Only after this check may #784 infer global native forbidden
avoidance. Then #764/#779 deliver the actual ordered Ramsey arrow
in a true maximal-trace age member.

### Genuine remaining bridge B4: all-arity/nullary compatibility

The current native Arrow/weak EHN infrastructure supports arbitrary
function arities, including nullary symbols. Some existing whole-mask
closure-profile and native iteration proofs assume positive arity or
a finite part set, or need a synchronized common nullary root. Any
specialization to Track E must either prove the required reduction
to the rooted/positive-arity language or make its restricted statement
explicit. Full JEP of all native structures also fails for incompatible
nullary interpretations; do NOT silently infer JEP from strong AP.

## Dependency graph

`#846 native↔partial full semantics`
  → `faithful whole-mask/full-order/tag encoding`
  → `certified corrected 2019 two-pass sparse construction`
  → `ambient-relative exact local completion transfer`
  → `#784 native forbidden avoidance`
  → `#764/#779 marked Ramsey target`

The ordered strong AP and irreducibility bridge run in parallel and
are needed wherever the relational theorem demands K strong AP and
irreducible members. The corrected two-pass construction—not a
generic native full-function mixed-rank increment—is the preferred
proof target unless one proves additional hypotheses eliminating
the explicit native counterexamples.

**Status:** English crosswalk/adversarial audit; NO complete finite-family
Ramsey theorem established by this document. Do not upgrade original
manuscript validation markers. Keep original numbered prose frozen.
