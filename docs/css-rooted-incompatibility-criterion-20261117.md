# Addendum: maximal profiles and finite rooted incompatibility

17 November 2026. English derivation; not Lean-certified. Assumptions and raw query family are exactly those of Section 8 of `css-finite-trace-locality-and-maximal-profiles-20261117.md`: finite positive relational signature, finite connected nonempty forbidden sources, possibly infinitely many forbiddens, and full old embeddings.

For a fixed finite allowed A, let G_A have as vertices finite allowed extensions of the labelled root A. Join two vertices when there is no allowed FULL amalgam over A, allowing extra relations, extra vertices and identifications outside the root. Since the language is relational, a finite amalgam exists whenever any amalgam exists: restrict it to the union of the two finite images.

Let M(A) be the inclusion-maximal feasible complete folded HE-query profiles as defined in the main note.

## 1. Finite M(A) colours the incompatibility graph

For each finite extension B/A, extend a witness of B to an allowed witness maximal on A. Colour B by its maximal A-profile. If B and C receive the same profile, the free old amalgam of their two witnesses is allowed by the source-transfer lemma. It contains full copies of B and C over A. Thus incompatible extensions have different colours and

    chi(G_A) <= |M(A)|

when M(A) is finite.

It is essential that the chosen maximal profile is realizable in an extension of the WHOLE B, not merely in an unrelated old structure with the same root. Cofinal maximalization from the main note supplies precisely this.

## 2. Distinct maximal profiles yield finite incompatibility cliques

Choose distinct t_1,...,t_m in M(A), with countable allowed witnesses W_i. No two W_i,W_j have an allowed full amalgam over A: any such amalgam has a feasible raw profile containing both, contradicting maximality and distinctness.

To extract finite witnesses, take the universal old-language theory T_K forbidding all HE maps from members of F, together with the full atomic diagrams of W_i and W_j. The constants naming A are shared; all other constants are allowed to be identified across the two diagrams. Inequalities inside each individual diagram enforce the injectivity of its embedding.

This theory has no model, because a model would be the disallowed amalgam. Compactness gives an inconsistent finite subset. Let B_i^(ij) and B_j^(ij) be the finite full induced substructures on the mentioned constants, enlarged to include all of A. They have no allowed full amalgam over A.

For each i take, INSIDE W_i, the finite full induced union B_i of B_i^(ij) for all j!=i. These B_i are allowed, contain A, and are pairwise nonamalgamable over A: an amalgam of B_i and B_j would restrict to an amalgam of the already incompatible pair B_i^(ij),B_j^(ij).

Hence m distinct maximal profiles produce a clique of order m in G_A. This works for every finite m, even if M(A) is infinite.

## 3. Exact finite-root conclusion

If M(A) has finite cardinality m, the two inequalities give

    omega(G_A) = chi(G_A) = |M(A)| = m.

If M(A) is infinite, G_A has arbitrarily large finite cliques. Consequently, for these HE-forbidden classes, the following three conditions are equivalent for each finite A:

- M(A) is finite;
- G_A is finitely colourable;
- there is a finite upper bound on the size of a pairwise nonamalgamable family of finite extensions over A.

Combining with the main note's transfer-based criterion gives the equivalence between a precompact exact-shadow relational Fraisse lift and any of these conditions holding at EVERY finite old root.

This is NOT a general graph-theoretic assertion that bounded clique number implies finite chromatic number. The implication for this specific incompatibility graph uses countable maximal witnesses, compactness, and source-transfer amalgamation. Nor is it a proof that the original piece-regularity hypothesis implies one of these properties. That bridge remains separate.

The statement identifies rigorously the intended role of regularity: it must bound actual persistent rooted incompatibility. For a finite forbidden family, the finite set of raw trace atoms guarantees the bound; for the proposed infinite family, permanent independent half-choices would force its failure if the concrete construction's hypotheses survive full validation.
