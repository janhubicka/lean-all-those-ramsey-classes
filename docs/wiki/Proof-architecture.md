# Verified corrected theorem: proof architecture

The theorem `AllThoseRamseyClasses.Published.coordinated2019_theorem218`
is a Lean-verified **alternative proof** of the coordinated corrected
2019 relational multiamalgamation result. It does not validate the
old native generating-rank induction in the published Lemma 2.30.

## 1. Begin with a closed Ramsey Picture

Fix a finite B in K and an arbitrary original control C0 in R.
Choose n(B,C0) before constructing the weak candidate. The verified
corrected Lemma 2.28 supplies the initial U-closed Ramsey Picture,
covering closed U-irreducible tests. The original C0 is not assumed
U-closed.

Lean: `Published/InducedClosed2019UnrestrictedInitial.lean`.

## 2. Replace invisible closures by explicit profiles

A generated-closure profile records an actual **closed substructure**
of B and its generators. Full embeddings of closed structures lift
with full relation reflection; profile boundaries from overlapping
pieces identify a genuine common closed K-object.

Lean: `Published/GeneratedClosureProfiles2019.lean` and
`Published/GeneratedClosureProfileBoundary2019.lean`.

## 3. Strict-tree sparsening and real K-amalgamation

Apply the pinned dependency's purely relational strict-tree
sparsening theorem to the profiled Picture. Two pieces are amalgamated
over the same real closed boundary with two compatible full
embeddings. K's strong amalgamation completes strict trees.
No arbitrary root-completion oracle is introduced.

Lean: `Published/ProfileStrictTreeCompletion2019.lean`.

## 4. New closure-root tags and a second closed pass

The sparse profile reduct may fail original root closedness.
Introduce a distinct fresh closure symbol for every compatible
expanded full root pattern and run the closed Picture construction
again. Prove tag normality, U-closedness and B-copy coverage before
forgetting the auxiliary symbols.

Lean: `Published/ProfileRootTagLanguage2019.lean`,
`ProfileRootTagClosedness2019.lean`,
`ProfileRootTagLocalLaws2019.lean` and
`ProfileRootTagTransfer2019.lean`.

## 5. Recover condition (4c) on the original weak S

For **each original exact weak induced subset** S with |S| <= n,
project its exact image (of cardinal at most |S|) into a profiled
strict tree and produce a genuine finite K-completion of that tree.
Closed-irreducible B-copy coverage upgrades the map to the required
protected map on S itself. Do not replace S with its closure hull.
The chosen same-cutoff local axiom gives a completion respecting
all B-copies; copywise Ramsey transfer completes the proof.

Lean: `Published/Coordinated2019ProfileSparseWitness.lean`.

## Unproved aspects of the original proof

The native rank-increment approach still needs a valid induction
over rank when transversal copy ranges have weak intersections and
separator vertices appear. That remains a **separate** original-proof
audit, not a hidden premise of the verified profile theorem.
The primitive-function formulation also requires its own precise
transfer from relational closure descriptions.

For a detailed complete English proof see
[the source proof note](../../docs/coordinated-profile-proof-20261013.md),
and for the native rank audit see
[the Lemma 2.30 note](../../docs/lemma230-detailed-english-native-proof-20261013.md).
Complete theorem CI: [run 38479503776](https://github.com/janhubicka/lean-all-those-ramsey-classes/actions/runs/38479503776).
