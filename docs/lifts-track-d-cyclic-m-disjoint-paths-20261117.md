# Track D: m disjoint short-nonedge paths (all m)

For the cyclic base Gamma_m, adjacency on natural representatives is |x−y|∈[m,2m−1]. For any short nonedge (0,d), 1≤d<m, there are exactly m explicit internally disjoint paths indexed i=0,...,m−1:

* if i<d, path 0,m+i,2m+i,d
* if d≤i<m, path 0,m+i,d

The new module supplies four all-m Lean source proofs: the two edge/finite-range path obligations, pairwise interior separation of different indices and absence of endpoints from any interior. The required property is stronger than an arbitrary 3-path: it is the constructive m-path witness behind the **English** proof κ(Γ_m)=m. To obtain the global native vertex-connectivity theorem, still formalize reflection and cyclic translation of these paths and then the elementary pigeonhole argument for deleted sets of cardinality <m.

An independent checker constructed all such paths for every ordered pair of nonadjacent vertices in Γ_m for m=3,...,23, verifying adjacency, interior endpoint-avoidance and pairwise interior disjointness. 23,772 ordered pairs passed; this is a computational check, not Lean certification of the global m-connectivity statement.

This is stacked on the all-m cyclic-threshold arithmetic PR #1275 and must remain DRAFT until the parent exact-head Lean build and this branch exact-head Lean/axiom/inventory/source checks pass. Neither the infinite native forbidden family nor its image-closure/regularity is fully formalized by these stand-alone lemmas. Frozen numbered manuscript untouched.
