# Projected-boundary saturation — 13 October 2026

This is a general improvement of the corrected 2019 mixed-cut gluing argument, not a proof of the unrestricted Picture increment. The implementation is PR #190. Its verification status must be read from the recorded CI result, not inferred from this English proof.

## Statement

Let F be a relational structure with a genuine free induced cover on vertex sets S and T. Thus S union T is the entire original carrier, and every relation tuple of F lies wholly in S or wholly in T. Neither F nor either side nor the original separator S intersection T is assumed U-closed or U-semi-closed.

Let p:F -> D be a corrected protected homomorphism, and suppose D is finite and U-closed. Assume K has finite strong amalgamation, is hereditary for closed substructures, and consists of ordinarily irreducible structures. Let A be a closed member of K with a full embedding a:A -> D. Suppose p(S intersection T) lies in this actual embedded A-copy.

Write

    H  = cl_D(p(S intersection T)),
    DL = cl_D(p(S)),
    DR = cl_D(p(T)).

If the ORIGINAL induced target structures D|DL and D|DR have corrected K-completions, then the ORIGINAL source F has a corrected K-completion. The map p need not be injective, F need not have maximal generating rank, and its original separator need not be closed.

In particular, the old rank-j completion invariant suffices whenever the two ORIGINAL projected side hulls have U-size at most j. Those two bounds remain hypotheses.

## Complete proof

### 1. Fix the target boundary before choosing completions

The embedded A-copy is relatively U-closed in D, because A is intrinsically closed, D is semiclosed, and the embedding is full. Consequently H is contained in that copy. Since D is closed, D|H is intrinsically closed. Closed heredity gives D|H in K; hence it is ordinarily irreducible by the class hypothesis. Closure monotonicity gives H contained in both DL and DR.

This constructs ONE specific closed K-boundary in the old target. It is not an arbitrary completion of the weak original source separator.

### 2. Enlarge the two source sides, not the source

Put Q=p^-1(H), Splus=S union Q, and Tplus=T union Q. These remain subsets of the ORIGINAL carrier of F. They cover it. Since p(S intersection T) is contained in H,

    Splus intersection Tplus = Q.

Every original source relation tuple was wholly in S or wholly in T, so it remains wholly in Splus or wholly in Tplus. Therefore the enlarged induced sides form a genuine free cover of F over F|Q. No tuple is deleted, and no new source vertex or relation is added.

### 3. Prove relative closure of the enlarged sides

Consider an existing closure tuple in F whose designated root lies in Splus. Tuple locality places the whole tuple in S or in T. In the former case all outputs are already in Splus. In the latter case, each root vertex either belongs to Q or belongs to S intersection T. Its p-image therefore belongs to H in both cases. Positivity of p makes the image a closure tuple in D. Relative closure of H puts every image output in H, so every original output belongs to Q and hence to Splus. Thus Splus is relatively U-closed in F. The argument for Tplus is symmetric.

The argument uses only actual existing source closure tuples. It does not invent a source output from a root, and it does not require F to be intrinsically closed. Accordingly it applies to the original weak tests.

### 4. Show that saturation adds no projected closure points

Since H is contained in DL, every point of p(Splus) lies in DL: the old S-points do by definition of DL, and added Q-points project into H. Minimality of closure gives cl_D(p(Splus)) contained in DL. The reverse inclusion follows from S contained in Splus. Therefore

    cl_D(p(Splus)) = DL,
    cl_D(p(Tplus)) = DR.

These are equalities with the ORIGINAL projected side hulls, not estimates that silently omit the common boundary. Saturation incurs no additional rank beyond those original hulls, but those original ranks might already be large.

### 5. Complete the two targets independently and amalgamate

Restriction and factorization of the corrected protected map give protected maps F|Splus -> D|DL and F|Tplus -> D|DR. The common source F|Q maps by p into D|H, and its two maps into the side targets factor through the actual full embeddings D|H -> D|DL and D|H -> D|DR.

Choose the assumed corrected K-completions of D|DL and D|DR. Each completion map restricts to a FULL embedding on D|H: that boundary is closed and ordinarily irreducible, hence a protected test. Strong amalgamation identifies these two full boundary embeddings. The resulting two maps agree on the exact source intersection Q.

The source free cover proves positivity of the glued map. A closed U-irreducible embedded source test lies wholly in one enlarged side: the inverse images of the two relatively closed ranges give a free cover by intrinsically closed substructures of that test, and U-irreducibility forces one side to be the entire test. Thus the glued map is full on every protected source test. The target belongs to K and is finite and ordinarily irreducible, so it is the required corrected completion of F.

Notice that F|Q itself need not be intrinsically closed and need not belong to K. Strong amalgamation occurs over the separately constructed actual target boundary D|H, not over F|Q.

## Lean declarations

All declarations are in namespace `AllThoseRamseyClasses.Published`.

`ProjectedBoundarySaturation2019.lean` contains:

- `positive2019_boundary_saturates_left`;
- `projected2019_saturation_preserves_hull`;
- `inducedClosed2019_completion_of_saturated_projected_cover`.

`ProjectedBoundaryHullGlue2019.lean` contains:

- `projected2019_separator_saturation_preserves_both_hulls`;
- `inducedClosed2019_completion_of_projected_hull_cut`;
- `inducedClosed2019_completion_of_projected_rank_cut_without_closed_root`.

The generic saturated-cover theorem also permits weak independent target sets L0,R0, provided both contain the same closed target K-boundary H. The hull theorem above is its specialization. The audit file lists all six declarations.

## What this removes, and what it does not

The old mixed-cut contract demanded an intrinsically closed source separator and semiclosed source sides. The new contract does not. Within a genuine common-projection cut with a separator inside a closed K-copy, source closure can be repaired by saturation without changing either projected target hull.

This does NOT produce a common protected map into the old Picture in native histories where only separate ordinary side maps have been constructed. It does NOT turn a false two-line COPY cover into a free cover. It does NOT show that the original projected side hulls have rank at most j. It does NOT justify ordinary weak-vertex-size induction as closed generating-rank induction.

For the rank-increment application the remaining geometric task is therefore to produce a genuine source cut and a suitable common protected projection, place its projected overlap inside one actual closed K-copy, and bound BOTH original projected side hulls by j. The unrestricted Theorem 2.18 remains partial.

## Provenance correction

The actual squash merge of verified cutoff-two PR #188 is `e8684e297974b0bfc0f63920892ccaf8c6a93f2d`, as returned by the live PR metadata. The previously recorded `daec134f9400f8816e4d89b07f7327074cd24d52` was a transcription error. Its checked proof head `f0395a205022a145f2f84efbc7bea6740039d03b` and successful CI run `38461482875` are unchanged.
