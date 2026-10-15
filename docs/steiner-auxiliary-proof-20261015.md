# Freely ordered partial Steiner triples — proof development

**Scope:** an auxiliary class **not** listed among the 2019 paper's examples.
Source modules: `Applications/SteinerTripleClass.lean`,
`SteinerStrongAmalgamation.lean`, `SteinerLocalCompletion.lean`.
This explanatory note describes the intended proof; only CI-green
declarations should be cited as formally validated.

## Exact encoding

The language has an order relation, an increasing covered-pair marker
and a ternary block relation. Each increasing marked pair has exactly
one ternary output, while unmarked pairs have none. For every block,
the corresponding markings of its other two pairs are present in their
increasing orientations. Full relational embeddings therefore reflect
both block tuples and the *domain* of the partial block operation.
Unlike ordinary hypergraph induced embeddings, they are strong Steiner
embeddings.

The closure description contains the unique rule with irreducible
two-vertex root `pairRoot` consisting of an increasing marked pair.
Its output symbol is `.block`.

## Strong amalgamation (PR #235)

Take an actual strong free relational amalgam (G) of two members over
a common full subsystem. All marked-pair and block tuples of (G)
occur entirely in an input side; there are no mixed positive tuples.
The already verified closure free-amalgam lemma proves that (G)
is closed under the marked-pair rule: each valid root still has
precisely one block output, even if the root is common to both sides.
The verified compatible-order construction extends both old linear
orders to a single total order on the *same vertex amalgam*.

Define the target by keeping (G)'s covered-pair and block predicates
unchanged and using this new total order. Every positive covered pair
lies in one side, so it is increasing. Similarly each positive block
and all of its other-pair rotations belong to one side. The inherited
block is nondegenerate and uniquely determined by its pair. Both side
maps preserve and reflect every relation, since their original orders
are total and the new order extends both. Vertex overlaps remain
exactly the given common subsystem. This proves genuine finite strong
amalgamation.

## Exact local completion: why cutoff zero should suffice (PR #236)

Fix *arbitrary* original finite ambient Ramsey control (C_0), a
member (B) of the Steiner class, and a finite **weak** candidate (C)
in the corrected 2019 local axiom. Assume:

- (C) is intrinsically closed under the marked-pair closure rule;
- (C) has a revised protected map (f:C	o C_0), possibly
  noninjective and with no requirement that (C_0) be closed;
- every **exact** closed U-irreducible induced substructure of (C)
  belongs to the Steiner class.

There is no global order or Steiner consistency assumption on (C)
apart from these premises.

**Tuple-hull lemma.** Fix any *positive* tuple of a relation symbol
of (C) (including `.order`, `.covered`, or `.block`).
The exact induced substructure on the vertices appearing in the tuple
is ordinarily irreducible. Take its closure hull (H) in (C).
Because (C) is closed, (H) is closed. By the upstream
`IsUClosed.irreducibleSeed_hull_isUIrreducible` theorem,
(H) is intrinsically U-irreducible. The corrected (4b)
membership premise puts **this entire induced (H)** in the
Steiner class. This use of a closure hull is only a *local test for
validity of positive tuples*: it never replaces any of the original
weak subsets tested in (4c).

The map (f) sends every old positive vertex-order pair to a
*strict* increasing pair in (C_0). Equip (C_0) with its ambient
linear order and lexicographically order (C)'s vertices by
((f(x),i(x))), where (i) is an arbitrary injective finite index.
This is total and extends every old positive order comparison.

Keep the non-order predicates of (C) unchanged and use the new
order for the target (D). On any tuple hull (H), the old order
is already total by (Hin K), so the new order coincides with
it. The inclusion of (H) into (D) is therefore a **full
relational embedding**. The tuple-hull lemma transfers all positive
local normal-form laws for the covered-pair and block predicates
from valid (H)'s to (D). The only apparently two-tuple law,
uniqueness of the block over the same marked pair, already follows
globally from intrinsic U-closedness.

Thus (Din K). Every original full copy of (B) in (C)
has a total old vertex order and survives fully in (D). The
identity map on the unchanged vertex set is a **B-copywise
completion**. We did not use the weak-small-test assumption (4c):
the specific Steiner class therefore satisfies the required local
implication with fixed cutoff **(n(B,C_0)=0)**.

This is special to the presentation where every non-order law is
controlled by a positive tuple's closed irreducible hull; it does
not claim that the general multiamalgamation theorem can omit (4c).

## Final Ramsey implication and audit boundary

Once both Lean modules compile and their named theorem axiom audits
pass, the class has all inputs to the **revised relational**
Theorem 2.18: ambient ordered Ramsey, irreducibility of its linear
order, subclass/finite/closed/hereditary/isomorphism invariance,
strong amalgamation and the exact local implication above. The
resulting theorem is
`AllThoseRamseyClasses.Applications.SteinerTriples.orderedSteiner_isRamsey`.

This is a separate extension to the formalized 2019 theory.
In particular, the native rank-increment Lemma 2.30 is neither
used nor claimed to have been reconstructed.
