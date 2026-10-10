# Literal Theorem 2.18: singleton vacuity and a paired-equivalence obstruction

**Source:** independent three-page note dated 9 October 2026,
`literal-2019-counterexample.pdf`, supplied with the published article.
This file documents the mathematics; a complete Lean theorem-level
counterexample remains unfinished until all class hypotheses are formalized.

## Exact 2019 interpretation

Definition 2.15 defines `U`-irreducibility by *nonexistence* of a free
decomposition into two proper intrinsically `U`-closed substructures.
The tested structure itself need not be `U`-closed. Every relational
singleton is thus `U`-irreducible (indeed ordinarily irreducible).

Suppose `K` has no one-vertex members. Then published Definition
2.17(4b) on an `U`-closed `C` forces `C` empty: if `x ∈ C`, its
singleton induced structure is `U`-irreducible and so would belong
to `K`, a contradiction. Consequently for any `B ∈ K` the empty
candidate has an automatically valid copywise `B`-completion. The
printed local-finiteness axiom holds with `n(B,C0)=1`, ignoring
(4a) and (4c). This is an excessively weak hypothesis, not a valid
positive local finiteness proof.

## Explicit candidate K

Language: strict linear order `<`, an equivalence `E`, and an
irreflexive symmetric perfect matching `M`, contained in `E`.
There is no convexity constraint. `R` consists of all finite ordered
relational structures with arbitrary `E,M`.

The closure rule has symbol `M` with singleton root `S` satisfying
`E(s,s)`, `¬M(s,s)` and `¬(s<s)`, so the unique `M`-output of a
root is its mate. Members of `K` are `U`-closed. Closed induced
substructures are exactly unions of matched pairs. Strong amalgamation
preserves the matching, takes the transitive equivalence closure of
the union of the two `E` relations (without changing either
restriction), and extends the two linear orders. A formal proof of
these class-level claims remains to be implemented in this repository.

## Persistent colouring

`A`: four ordered vertices, consecutive matching pairs of
equivalence-class pattern `X,Y`. `B`: six ordered vertices,
consecutive matched pairs of pattern `X,Y,X`.

Label the `E`-classes of a finite target `C` distinctly. Colour
each `A`-copy according to the comparison of the labels of its two
classes. The first two and last two matched pairs in every `B`-copy
form `A`-copies with opposite colours. Thus no `C∈K` satisfies
`C → (B)^A_2`.

The finite labelled A/B structures and global colouring obstruction
are formalized from an *unverified* draft source in
`Published/PairedEquivalences.lean`; they will only receive
GREEN markers after this repository's CI and axioms checks succeed.

## The suggested repair is substantive

Do not silently redefine the literal 2019 interface. A candidate
separate interface tests **U-closed U-irreducibles** in (4b),
and asks map restrictions to embed all such closed tests. Retain
EVERY exact weak induced test in (4c), not just closed tests; the
quantifier is genuinely about at most `n` tested vertices.
This repairs the singleton vacuity at the *hypothesis* level,
but **does not by itself prove** the corrected main theorem.
The semi-closed intermediate Picture stage and higher-rank
boundary-aware increment remain open in `partite-construction`.
