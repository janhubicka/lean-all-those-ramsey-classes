# Track C — exact SOURCE gain/loss law for a native selected-Q flip

15 November 2026. Stacked on #1206 -> #1204, draft pending
exact-head Lean, permitted axioms, no-admission/source-integrity
and protected active-root checks. Frozen original 2019 source unchanged.

The old original finite F-forbidden source has the **disjoint**
native source partition of each chosen target support region
Active into:

  retained E Active SOURCE vertices
  ⊔ old removed selected-component Active SOURCE vertices.

The full new Q+_R E source has the **disjoint** partition from
#1204 and the exact cardinality formula from #1206:

  retained E Active SOURCE vertices
  ⊔ NEW inserted Q-nonroot Active SOURCE vertices.

Since the old/new weak target coordinates coincide on ALL E,
the exact finite Nat.card identity is

  NEW Active SOURCE count + OLD deleted-component Active count
    = OLD Active SOURCE count + NEW private-Q Active count.

It is valid for ANY fixed target support region Active: the
old removed component need NOT be A-free. In particular,
on the RIGHT/B-exclusive target region of the true B-to-A
selected-Q flip, the already-verified same-selected-Q
no-new-B certificate says Q has NO new B source vertices.
The exact B-source loss is therefore

  NEW total B support + B support in the deleted old component
    = OLD total B support.

On the LEFT/A-exclusive target region of a selected A-free
old component, the old deletion term is zero; the exact
equation specializes to A-growth by the private Q-A SOURCE
cardinality derived separately in #1206.

Together these are the actual quantitative two-sided
B→A flip accounting, with no arbitrary target-image
identifications or weak target-map global injection.

This module does NOT claim a weight makes the vector
(A_total, B_total) decrease on every selected Q: an arbitrary
canonical Q may have many new A-active nonroots. It identifies
the exact missing inequality for any proposed amortized
potential and is not a proof of unrestricted Claim 2.

Three named #print axioms and protected active-root entry.
No collaborator-removed TODOs reinstated.

## Exact weighted-potential descent criterion

The module also now proves a purely numerical lemma and its genuine
selected-Q source specialization: for any weight k >= 0, when the
old removed selected component is A-free and Q contributes no new
B-active vertices,

  (B_new + k*A_new < B_old + k*A_old)
    IFF (k*A_private_Q < B_removed_old_component).

This is a *necessary and sufficient* source-cardinality inequality
for that weighted potential, on one selected Q, not a statement
that some k or every canonical Q makes it hold. The exact
arithmetic uses the proven A-cost and B-loss identities;
no unsupported weak target-map injection or quotient counting.

In particular, even k=1 requires the number of NEW A-active
private Q source vertices to be strictly smaller than the
OLD B-active source vertices deleted. Without a bound of this
kind an amortized source-weighted descent cannot be claimed.
