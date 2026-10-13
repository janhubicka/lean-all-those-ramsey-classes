# Coordinated 2019 theorem: profile sparsening and a final closed pass

This note gives the alternative proof implemented in PR #195. Its verification evidence is maintained separately in `docs/current-main-theorem-status.md`; a mathematical proof description is not itself a CI certificate. All declarations named below are in `AllThoseRamseyClasses.Published` unless another namespace is displayed.

## Exact statement and scope

Let L be a relational language with closure description U. Let R be a Ramsey class of finite ordinarily irreducible L-structures, and let K be an isomorphism-invariant subclass satisfying the coordinated corrected multiamalgamation conditions: K-members are U-closed; K is hereditary for U-closed substructures and has finite strong amalgamation; and the locally finite completion condition uses the corrected protected maps and corrected closed-irreducible membership tests. Then K is Ramsey.

The corrected map tests are exactly induced structures which are BOTH intrinsically U-closed and intrinsically U-irreducible. Intrinsic U-irreducibility has not been changed. Clause (4c) continues to quantify over EVERY original weak induced subset with at most the preselected n(B,C0) vertices. No generated hull replaces a tested subset.

The formal endpoint is `coordinated2019_ramsey_by_profile_sparsening` in `Coordinated2019ProfileSparseWitness.lean`. Its hypotheses are precisely `FiniteRamseyClass R`, ordinary irreducibility of members of R, and `IsCoordinated2019MultiamalgamationClass R K rules`, whose established interface explicitly includes isomorphism invariance. It has no native rank-increment, compatible-boundary, or sparse-witness constructor premise.

This is the corrected RELATIONAL closure-description formulation. It is not the literal published theorem, which has a checked counterexample. It is also not a verification of the original native generating-rank argument in Lemma 2.30. A separate claim about every formulation involving primitive functions must identify its relationalization bridge; it should not be inferred merely from the name of this endpoint.

## 1. Fix the original control and cutoff before constructing anything

Fix finite A,B in K and a nonempty finite colour set. The Ramsey property of R supplies the original control C0 in R with C0 -> (B)^A. Now choose n=n(B,C0) from the corrected local-completion axiom. Neither C0 nor n will be changed later.

The already constructed unrestricted closed Picture theorem, corresponding to corrected Lemma 2.28, supplies a finite U-closed D with D -> (B)^A and a corrected protected projection D -> C0. The original C0 need not be U-closed. This is an actual construction, not the formerly open initial-Picture premise.

It remains to build a finite U-closed Q with the Ramsey arrow, a corrected protected map to the same C0, membership in K of every closed U-irreducible induced test, and K-completions of all original weak tests on at most n vertices.

## 2. Record generated closed boundaries before sparsening

A profile consists of an actual U-closed induced substructure H of the fixed B, together with a finite tuple g generating H intrinsically. Add a relation symbol R_(H,g) of the tuple's length. In the canonical expansion E+ of an L-structure E, declare

    R_(H,g)(x)  iff  there is a FULL embedding e:H -> E with e(g)=x.

Retain every original symbol, including nullary symbols. The implementation permits all finite tuple lengths and does not claim that the auxiliary signature is finite. The two construction theorems invoked here have no finite-signature hypothesis.

**Embedding lemma.** Every full embedding f:E -> F between U-closed structures lifts to a full profile embedding E+ -> F+.

Preservation follows by composition. For reflection, suppose a full realization a:H -> F sends every generator of H into f(E). The image f(E) is relatively U-closed in F. Its preimage under a is a relative U-substructure of H containing all its generators, and therefore all of H. Consequently a(H) is contained in f(E), and factoring through the full embedding f gives a full realization in E. This is not an extension of an arbitrary weak completion: the whole realized H is already present, and generated-range containment forces it into the required image.

The Ramsey arrow A+ -> B+ in D+ follows by lifting embeddings, colouring the lifts of original A-copies, and forgetting the resulting B+ copy. All three original structures are closed at this stage.

Every induced subset of B+ is ordinarily irreducible. Enumerate that exact subset and record its actual closure in B with the enumeration as generators. Its profile relation is a tuple on the original subset and witnesses all pairs there. No vertices of its closure have been added to the subset.

Lean: `GeneratedClosureProfiles2019.lean`, `GeneratedClosureProfileBoundary2019.lean`.

## 3. Strict profile trees have genuine finite K-completions

Consider a strict relational tree amalgam of copies of B+. At every gluing step, the common weak root M is embedded into an irreducible substructure on each side. In a strict tree, every such irreducible substructure lies in an actual constituent B+ copy. Thus the left root map factors through a full B+ copy. The root carrier is finite, because it embeds into the finite B.

Inductively, both sides already have maps into canonical expansions E1+ and E2+ of finite K-members, preserving all B+ copies as full embeddings. The two maps restrict to full embeddings on M, because M lies in actual B+ copies on the two sides.

Enumerate M, and use its left factorization into B to form the profile of the actual closed hull H of those vertices in B. The corresponding relation holds on that enumeration in the left B+ copy. Full reflection makes it hold in the EXACT common profile structure M; preservation along the right root embedding gives a full realization of the SAME H in E2. The left embedding into E1 comes from the actual B+ copy. Both embeddings agree with the old root maps on every original root vertex.

Since H is closed in B and B belongs to K, closed heredity gives H in K. Strong amalgamation of E1 and E2 over these two full embeddings of H gives a finite E in K. The old maps agree on M in E, so the actual free source diagram has a compatible fold into E+. The embeddings of E1 and E2 lift to profile embeddings because they are closed K-members. Every B+ copy lies on one side, since B+ is ordinarily irreducible, so this fold preserves all B+ copies.

Every relation tuple of the strict tree and every ordinary irreducible test lies in a constituent B+ copy. Hence the copy-preserving fold is an ordinary homomorphism-embedding. Composing with an ordinary homomorphism-embedding from any weak source into the tree gives that source a genuine finite canonical-profile K-target.

The common root need not itself be closed or belong to K. The proof constructs its compatible closed K-boundary from its shared profile. Empty roots and nullary data are included: full profile embeddings, rather than arbitrary empty maps, transport the corresponding records.

Lean: `ProfileStrictTreeCompletion2019.lean`, especially `closureProfile2019_tree_completion_to_K`.

## 4. Apply the existing purely relational sparsening theorem

Apply `StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all` to A+, B+, D+ and the ALREADY FIXED n. It produces a finite profile-language structure P, the Ramsey arrow P -> (B+)^(A+), an ordinary homomorphism-embedding p:P -> D+, and an ordinary strict-B+-tree completion for every exact induced subset of P with at most n vertices.

This is a purely relational theorem. It does not use the disputed closure-rank increment. The output P is not assumed to have an originally U-closed reduct and is not assumed to be the canonical profile expansion of its reduct. Those missing properties cannot be silently imposed.

## 5. Fresh tags recover original closedness after a second pass

For each original closure rule r and EVERY full profile-language pattern S on its root carrier whose original reduct is exactly r's prescribed root, introduce a DISTINCT fresh closure relation symbol. In the canonical tagged expansion of E, its relation means an old r-tuple whose root prefix fully embeds this exact full pattern S. The lifted closure rule has as root the canonical tagged expansion of S. It remains ordinarily irreducible because the original root's witnessing tuples are retained.

This fresh-symbol assignment is essential: distinct full root patterns must not share a single unchanged closure symbol.

Canonical tagging preserves and reflects full embeddings of arbitrary weak profile structures. For reflection the inverse root map is explicitly the original tuple prefix. It does not rely on either structure being closed. Therefore the arrow on P lifts to a tagged arrow. Canonically tagged A+ and B+ are closed under the lifted closure description, since their original reducts A and B are U-closed.

Apply the unrestricted closed Picture theorem a SECOND time, in the tagged language. Obtain a finite lifted-closed Q*, a tagged Ramsey arrow, a corrected tagged projection Q* -> P*, and coverage of all lifted-closed lifted-irreducible tests by the canonical tagged B*.

Two local laws must now be proved, not assumed:

1. Every fresh tag agrees with its canonical meaning in the profile reduct (tag normality).
2. Every old closure tuple has a valid ORIGINAL root.

Both laws are inherited by full embeddings. Each direction of normality, and old-root validity, concerns the support of a true relation tuple. That exact support is ordinarily irreducible. Its ambient lifted closure in Q* is lifted-closed and lifted-irreducible, so coverage embeds the whole closure into B*. Restriction supplies a full embedding of the original tuple support. The laws hold in B* and consequently on the support. This proves BOTH laws throughout Q*.

For an arbitrary original root embedding in Q*, take its actual full profile pattern S. Normality lifts it to the root of the corresponding fresh rule. Lifted closedness gives an old output tuple. All other old tuples with this prefix carry the same fresh tag by normality, so lifted uniqueness proves original uniqueness. Old-root validity rules out malformed old tuples. Thus the original reduct Q is genuinely U-closed.

Every original closed U-irreducible induced test also lifts to a closed irreducible tagged test. Closedness follows from original closedness and inherited normality. A hypothetical tagged closed free decomposition would have originally closed sides by both local laws; forgetting auxiliary relations gives a genuine original free decomposition, contradicting original U-irreducibility. Tagged coverage therefore embeds every such test into original B. Closed heredity puts it in K, and hence it is ordinarily irreducible.

Lean: `ProfileRootTagLanguage2019.lean`, `ProfileRootTagClosedness2019.lean`, `ProfileRootTagLocalLaws2019.lean`, `ProfileRootTagTransfer2019.lean`.

## 6. Recover maps, the original arrow, and all exact weak tests

Because Q* is lifted-closed, its corrected tagged projection is an ordinary homomorphism-embedding. Forgetting tags preserves ordinary homomorphism-embeddings, as does forgetting profiles: an ordinary irreducible test in a reduct remains irreducible when relations are added. Thus Q maps ordinarily to D through P.

For any original closed U-irreducible test of Q, the preceding coverage and closed heredity show that it belongs to K and is therefore ORDINARY irreducible. The ordinary map consequently embeds it fully. This turns Q -> D into the EXACT corrected protected map. Compose with the already constructed corrected map D -> C0.

The original Ramsey arrow also survives. Given a colouring of original A-embeddings into Q, colour tagged A*-embeddings by forgetting their auxiliary relations. Select a monochromatic B* copy. Every original A -> B embedding lifts canonically because both inputs are closed. Hence all original A-copies inside this B-copy have one colour. No claim that every global original A-copy of Q has a lift is needed.

Finally fix an ORIGINAL weak induced subset S of Q with |S|<=n. Map its profile expansion as inherited from Q* into its EXACT image T in P. This map is ordinary and |T|<=|S|<=n, even when the projection identifies vertices. The relational sparsening theorem supplies an ordinary map of P|T into a strict B+-tree. Section 3 then supplies an ordinary map to the canonical expansion of a finite E in K. Forget profiles to obtain an ordinary map of the ORIGINAL Q|S into E.

Every closed U-irreducible test of Q|S still embeds into B, by composing its embedding with Q|S -> Q. It therefore belongs to K and is ordinarily irreducible. The last ordinary map is consequently a corrected protected map on exactly those tests. Since E is irreducible, it is a genuine corrected K-completion of Q|S. The source remains S throughout the conclusion; no hull has replaced it.

This proves `coordinated2019_profile_sparse_witness` for every preselected n, including zero.

## 7. Apply the original fixed-cutoff local axiom

The finite Q now satisfies original closedness, a corrected protected projection to the SAME C0, the exact closed-irreducible K-membership clause, and completions of ALL original weak induced subsets on at most the SAME n(B,C0) vertices. Apply the coordinated local axiom to obtain a K-completion respecting B-copies. The existing B-copywise Ramsey transfer gives the required finite Ramsey target in K.

This completes the alternative argument. It does not prove the independent native rank-increment assertion or repair every sentence of the old proof.

## Audit boundaries and implementation correction

The reviewed final theorem has no hypothesis asserting the desired sparse witness or any rank promotion. Isomorphism invariance is explicit, as in the established corrected class interface. The proof uses finite structures in auxiliary signatures which need not be finite; the invoked Ramsey constructions allow those signatures.

The CI error observed in PR #195 at line 49 was a colour-universe mismatch between `κ : Type*` and the pre-existing sparse-witness contract's `κ : Type`. Commit `c783c23377d56d29bdfb7d61fe95e9c7e96073d2` restricts that wrapper binder to the contract's universe. It does not change the mathematical class, tests, or conclusion. A new complete CI/axiom audit is required for this head.

Provenance correction for the earlier cutoff-two result: GitHub PR #188 records squash merge `e8684e297974b0bfc0f63920892ccaf8c6a93f2d`, not `daec134f9400f8816e4d89b07f7327074cd24d52` as mistakenly written in an earlier status note. Its checked proof head `f0395a205022a145f2f84efbc7bea6740039d03b` and successful CI run `38461482875` are unchanged.
