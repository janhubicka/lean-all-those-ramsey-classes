# Track E: ordered strong amalgamation after full-functional strong AP

**Status: English proof / Lean integration not yet validated (3 November 2026).**

## Purpose and assumptions

The finite named all-closed-component maximal **induced-trace** age has
already passed full Lean CI for genuine **unordered** strong amalgamation
(`finiteNamedMaximalTraceAge_strongAmalgamation`), including full
set-valued-function fibres and exact overlap. Its ordered expansions
are intended as the target of a fully ordered strict-tree
completion. For that application we need **finite ordered strong AP**,
not an assertion that the new tag relations form a free amalgam.

The missing step is pure finite order theory. Given finite linearly
ordered carriers `X,Y,Z`, two **strictly increasing** full structural
embeddings `fY:X→Y` and `fZ:X→Z`, and a finite *unordered*
strong-amalgamation target `T` with full embeddings
`jY:Y→T` and `jZ:Z→T` such that

`jY(y)=jZ(z) ↔ ∃x∈X, y=fY(x) ∧ z=fZ(x)`,

construct one total linear order on T such that both jY and jZ are
strictly increasing. The construction must also work for empty X,
nullary symbols, and extra T-vertices, without modifying T's native
functions or any folded-tag predicate.

## A direct finite lexicographic construction

Fix arbitrary finite enumerations, independent of the actual orders,
to break ties for leftover vertices. Write

- `ρ(x) := |{u∈X : u<x}|` for root order rank;
- `rY(y) := |{x∈X : fY(x)<y}|` for the number of *shared root*
  vertices below an element y of Y;
- `rZ(z) := |{x∈X : fZ(x)<z}|` similarly.

The identity `rY(fY(x))=ρ(x)=rZ(fZ(x))` follows from strict
monotonicity of the common-root embeddings. Both cut ranks are
monotone on their respective ordered sides. Every target vertex
has exactly one category by the **actual strong-overlap law**:
a shared root vertex, a Y-private vertex, a Z-private vertex, or
a target-extra vertex. More specifically, the overlap law ensures
no vertex can be simultaneously Y-private and Z-private.

Assign to each t∈T a key in lexicographic `ℕ×ℕ×ℕ`:

| category | key |
|---|---|
| shared `t=jY(fY(x))=jZ(fZ(x))` | `(ρ(x), 2, ρ(x))` |
| Y-private `t=jY(y)` | `(rY(y), 0, rankY(y))` |
| Z-private `t=jZ(z)` | `(rZ(z), 1, rankZ(z))` |
| target-extra `t` | `(|X|+1, 3, arbitraryIndexT(t))` |

The middle coordinate orders all Y-private and Z-private elements
inside the same gap **before** the next shared-root element, as it
must: a private vertex with cut rank k lies after the first k
shared-root vertices but before the (k+1)-st. The precise ordering
between distinct Y-private and Z-private elements in the same gap
is irrelevant; choosing Y before Z causes no loss of either side's
internal order.

**Injectivity of the key.** A category is determined by the middle
coordinate. Within Y-private or Z-private vertices, the final
coordinate is an intrinsic rank and hence injective. Shared roots
have injective root rank; target extras have an injective arbitrary
enumeration. The classification of a vertex is unambiguous by the
strong-overlap law. Hence lexicographic key transport constructs
a linear order on all of T.

**Extension of the Y order.** For y<y' in Y, monotonicity gives
`rY(y)≤rY(y')`. If strict, the first key coordinate suffices.
If equal, y cannot be a shared root (its own root coordinate would
be counted below y' but not below y). If y' is a root, its
middle category is 2 and the earlier y has category 0.
Otherwise both y,y' are Y-private and the strict intrinsic rank
orders them. This proves `jY(y)<_T jY(y')`. The proof for Z
is identical, with its middle category 1. Order reflection then
follows from injectivity and totality of the side orders.

The target's native functional signature, all complete function
output fibres and its component-tag relation tables are unchanged:
only a fresh external order is adjoined. The resulting
`jY.withLinearOrder` and `jZ.withLinearOrder` are FULL
ordered functional embeddings; their original strong intersection
condition survives literally.

## Lean targets and dependencies

1. Pure lemma `exists_linearOrder_extending_two_embeddings`:
   input finite orders X,Y,Z, finite T, injections `fY,fZ,jY,jZ`
   and the exact strong overlap condition; output `o : LinearOrder T`
   and strict monotonicity of jY,jZ. No language or structure input.
   Use `Rooted.orderRank` and finite-cardinality lemmas from
   `PartiteConstruction.Structure.RootedOrder`; use
   `LinearOrder.lift'` on the injective lex key.
2. Structural corollary: `finiteNamedMaximalTraceAge` has ordered
   strong AP for its external freely ordered expansions, by applying
   the existing genuine unordered strong AP to the reducts,
   then the pure order-extension lemma. The input embeddings
   are FULL native/tag embeddings already; the final ordered
   embeddings reflect the strict order and all old functions.
3. Use this ordered strong AP to adapt the existing strictly
   functional tree-completion theorem (merged PR #774) to the
   ordered lifted language. The base is irreducible *because
   every two distinct vertices are comparable in the added order*,
   not because its unordered shadow is irreducible.
4. After that, prove the harder mixed weak local-test rank increment.
   Ordered strong AP and strict-tree completion do not by themselves
   convert a weak function-graph tree into a genuine strict functional
   tree. The actual selected support and whole function fibres need
   separate treatment.

## Adversarial checks and nonimplications

- Merely taking all Y-private vertices before all Z-private vertices
  **globally** can break the side orders when the common root
  interleaves vertices. Rank by shared-root cut FIRST.
- A root element is placed AFTER private vertices with the same cut
  rank, not before them. This choice is essential for extending
  the original orders.
- Do not replace a target-extra vertex by a root vertex; extras get
  a final separate key segment.
- Root images must agree not only as unordered sets but in their
  **same prescribed root order**, an input already guaranteed by
  full ordered embeddings of the common root.
- The overlap equivalence must be the exact strong law, not merely
  agreement of root images; otherwise a private Y vertex could
  coincide with a private Z vertex and the category-based argument
  would fail.
- The order extension does not require strong **free** AP of the
  expanded tag age, and must not be used to infer it.
- This is a finite-carrier construction and says nothing about a
  uniform bound on the size of maximizing witnesses.
- Proving ordered strong AP would NOT close the E2 sparse-control
  rank increment. In particular, the corrected ambient-relative
  weak-test semantics must be maintained.

Keep frozen `ramsey.tex` unchanged. Update review-only ATRC-072
after actual Lean proof gates pass, not on the strength of this
English note alone.
