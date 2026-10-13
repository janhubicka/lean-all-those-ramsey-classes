# A profile / relational-sparsening route to coordinated Theorem 2.18

**13 October 2026. Construction proof for audit; NOT a Lean certificate for the unrestricted theorem.**

The existing native closed-generating-rank increment remains unproved. This note develops a different construction, using the already checked purely relational sparsening theorem and a closure-record expansion. It may prove the corrected main theorem without proving the stronger native Lemma 2.30 constructor. These scopes must not be conflated. The working numbered manuscript is not replaced by this note.

The closure-record embedding and boundary statements are implemented in PR #192. The general tagged-closure lift and its connection to sparse weak tests are not yet formalized. Every arrow below is a mathematical proof obligation until its exact implementation is checked; the prose is not an axiom or a constructor instance.

## 1. Keep the original quantifiers fixed

Work with the coordinated definitions: map protection and K-membership concern precisely the intrinsically U-closed, intrinsically U-irreducible induced tests. The definition of U-irreducibility is unchanged. The local axiom must still test EVERY original weak induced subset of at most n vertices, not just closed tests or generator sets.

Fix A,B in K and a finite nonempty colour set. Obtain the original Ramsey control C0 in R. **Now select the original n=n(B,C0), before any auxiliary expansion or sparse witness.** All later maps must end at this same C0. Never invoke local finiteness again at a larger auxiliary control.

Use the already proved unrestricted initial Picture (corrected Lemma 2.28) to obtain a finite U-closed D with the Ramsey arrow, a corrected protected map p0:D->C0, and the original closed U-irreducible B-copy coverage. This construction is available even when C0 is not U-closed.

## 2. Record an actual generated closed structure, not merely its size

For a closed induced H of B and a finite tuple g generating H, introduce a relation P_(H,g) of arity length(g). In an arbitrary original structure E, declare

    P_(H,g)(x) iff there is a FULL embedding a:H->E with a(g_i)=x_i for all i.

Write E+ for this canonical expansion. Retain every original relation symbol, including nullary symbols. The implementation permits all finite tuple lengths, and makes no claim that the resulting symbol set is finite. For the proposed construction one could restrict to tuples of length at most |B|, but that finite-language refinement is separate work and is not assumed by the current code. The imported relational construction theorems themselves have no finite-symbol hypothesis.

### Full embeddings between closed structures lift exactly

Let f:E->F be a full embedding and assume both E and F are U-closed. Preservation of profiles is composition of full embeddings. For reflection, suppose a:H->F realizes the profile at f(x). The range f(E) is relatively U-closed in F. Its inverse image under a is relatively U-closed in H and contains every g_i. Since g generates H, this inverse image is all of H. Therefore a(H) is contained in f(E), and a factors through a full embedding H->E realizing the original tuple x.

This is a genuine containment/factorization proof. It does not assert that an arbitrary completion of x extends to a prescribed hull. Closedness of E is essential to the reflection argument.

Consequently all full embeddings between the closed inputs A,B,D lift, and the Ramsey arrow for A,B,D lifts to A+,B+,D+. No Ramsey property of the class of expansions is assumed.

### An arbitrary finite weak profile overlap gives a common closed boundary

Suppose a finite weak expanded structure J embeds fully into B+ on the left and E+ on the right. Enumerate ALL original vertices of J by a tuple t. In B, take H to be the actual closure of the left image of t. The same tuple, viewed in H, generates H. Its profile is true in B+, hence true in J by reflection through the left full embedding, hence true in E+ by preservation through the right embedding. Thus there is a FULL embedding H->E matching every original vertex of J. The left embedding H->B is inclusion. Closed heredity gives H in K when B is in K.

This derives two full embeddings of ONE closed K-boundary, agreeing through a map J->H. The weak common structure J need not be closed or irreducible. The assertion is valid for matching PROFILE overlaps, not automatically for unexpanded overlaps.

For finite closed B, B+ is even hereditarily ordinarily irreducible: a profile on an enumeration of any induced vertex subset supplies a relation tuple containing every pair in that subset. This observation does not change the vertex set of the tested weak subset.

## 3. Complete strict relational trees of B+ in canonical K-expansions

**Mathematical induction proposed here; not yet a checked Lean theorem.**

Claim: every strict relational tree amalgam T of copies of B+ has an ordinary homomorphism-embedding into E+ for some finite E in K.

The base is a copy of B+. For a free gluing T=T1 amalgam_J T2, strictness places each root image inside an ordinary irreducible substructure of its side. The checked tree-containment theorem places that substructure in a full B+ copy. Factor both embeddings of J through these B+ copies. Their root carrier is finite because it embeds into finite B.

Use Section 2 to construct one closed H in K and full embeddings H->B into both chosen copies, matching every original root vertex. The inductive ordinary homomorphism-embeddings T_i->E_i+ restrict to full embeddings on these B+ copies, since B+ is ordinarily irreducible. Forget profiles there, and compose to obtain two full embeddings H->E_i.

Apply the actual finite strong amalgamation property of K over H, producing finite E in K and full embeddings E_i->E that agree on H. Both E_i and E are U-closed by the class hypothesis, so these embeddings lift to full canonical profile embeddings by Section 2. The two resulting ordinary maps on T1,T2 agree on the original weak root J. Their free fold is positive because every source relation tuple belongs to one side; it is a homomorphism-embedding because every ordinary irreducible source test lies wholly on one side.

No target freeness or global injectivity of the folded map is required. Additional identifications forced by gluing the closed H rather than the weak J are permitted outside protected irreducibles. The argument also retains nullary relations because every boundary map used is a full embedding.

## 4. Apply the checked PURELY RELATIONAL sparsening theorem

Apply

    StructuralRamsey.Partite.IteratedSparsening.sparseningRamsey_strict_baseIrreducible_all

in the profile language to A+,B+,D+ at the already fixed n. It supplies a finite relational P+, the corresponding Ramsey arrow, an ordinary homomorphism-embedding P+->D+, and strict B+-tree completions of every exact induced subset of P+ on at most n vertices.

The theorem is in the pinned `PartiteConstruction/Iterated/SparseningStrictBaseIrreducible.lean`. Section 3 would convert those strict-tree completions to ordinary maps into canonical K-expansions.

**P+ is not asserted U-closed.** Neither weak-test tree completions nor profile predicates alone justify that assertion. The following additional closed pass is essential.

## 5. Lift closure through arbitrary relational expansions using FRESH tagged symbols

This is the largest remaining formalization bridge. It is a generalization of the already checked root-tagged unary-part construction, not a reuse of an unchanged original closure symbol with several incompatible root descriptions.

Let L+ be the profile language. For each original rule r, with root size k and original closure-relation symbol R, and each L+-structure Q on k vertices whose original reduct is exactly the prescribed root of r, introduce a DISTINCT new symbol T_(r,Q) of the same arity as R.

For an arbitrary L+-structure E+, define its canonical tagged expansion by

    T_(r,Q)(z) iff R(z) and the first k coordinates of z define a FULL embedding Q->E+.

The lifted closure rule for T_(r,Q) has root equal to the canonical tagged expansion of Q. Its root is ordinarily irreducible because the original root was and all original relations remain. Its positive/proper root arity conditions are inherited from r. Include all compatible root patterns Q, not only the patterns currently known to occur in B, to avoid an unproved root-type omission argument.

Tagging preserves and reflects all full embeddings: the defining condition is local to the displayed tuple and its prefix. It therefore lifts the Ramsey arrow from A+,B+,P+ to their tagged expansions, without requiring P+ closed.

### The necessary local laws

For an arbitrary tagged structure X, use both of the following laws.

**Tag normality:** each tagged relation is exactly the formula above in the reduct obtained by forgetting tags.

**Original root validity:** every tuple in an OLD closure relation has a prefix defining a full embedding of its original prescribed root.

Both laws hold in a canonical tagged expansion of an originally U-closed structure. Both are inherited by full induced substructures and invariant under full embeddings. Importantly, tag normality alone does not imply old root validity: an old closure tuple with an invalid root can carry no matching tag. Bare lifted closedness must NOT be silently used to infer original closedness.

### Closedness equivalence on structures satisfying the local laws

If the original reduct is U-closed, canonical tag normality gives lifted closedness: an embedded tagged root forgets to its pattern Q and hence to an original root; the unique original closure tuple has that same prefix pattern and acquires the corresponding tag. Uniqueness comes from original uniqueness.

Conversely, suppose X is lifted-closed, tag-normal, and old-root-valid. Original validity is already present. Given an embedded original root e, let Q be the ACTUAL full L+-structure induced by e on its k coordinates. Normality lifts that full embedding to the tagged root. Lifted closedness produces a tagged closure tuple, hence an old closure tuple, over e. Every other old closure tuple over e has the same ACTUAL prefix pattern Q and hence the same tag by normality; lifted uniqueness makes it equal to the first. Thus the original reduct is U-closed.

The same proof applies to every full induced substructure satisfying the inherited local laws.

## 6. The final closed Picture enforces the two local laws

Apply the already constructed unrestricted closed Picture theorem in the tagged language with the lifted closure description, closed tagged A and B, and the possibly nonclosed tagged P as control. Obtain a finite lifted-closed Qtag, a corrected lifted protected map q:Qtag->Ptag, the tagged Ramsey arrow, and lifted-closed lifted-irreducible Btag-copy coverage.

To derive normality and old root validity in Qtag, inspect the support of a tuple in an old closure relation or in a tagged relation. That support is ordinarily irreducible because the tuple contains all its vertices. Its lifted closure in Qtag is lifted-closed and lifted-irreducible. Coverage therefore embeds this ACTUAL closed hull fully into Btag. Restrict to the original tuple support and transfer the local law from Btag. For the backward direction of normality, use the old closure tuple to obtain the same support embedding, then reflect the appropriate tag. No tuple support is substituted for the weak tests of the local-completion axiom.

Section 5 now implies that the original reduct Q is U-closed.

Further, let F be an original U-closed U-irreducible induced test of Q. Its inherited expansion satisfies the local laws and is lifted-closed by Section 5. Any nontrivial free decomposition into lifted-closed pieces would forget to a nontrivial free decomposition of original F into U-closed pieces: the local laws pass to those full pieces and Section 5 gives their original closedness. Thus F's inherited tagged expansion is lifted-irreducible. Btag-coverage embeds it into Btag, so F embeds into B and lies in K by closed heredity.

This supplies the exact membership clause (4b). In particular every such F is ordinarily irreducible because all K-members are.

## 7. Preserve the ORIGINAL weak tests and the ORIGINAL control

A lifted protected map with lifted-closed source is ordinary on all ordinary irreducible weak tests: first extend such a test to its actual lifted closure, use protectedness on that lifted-closed lifted-irreducible hull, then restrict. This is the same safe hull-first restriction principle already used in the earlier native weak-test bridges.

Hence q is an ordinary homomorphism-embedding. Forgetting tags preserves this property, and composition with P+->D+ gives an ordinary map from Q's inherited profile expansion into D+. Forget profiles to obtain an ordinary map Q->D. It is also corrected U-protected: every original closed U-irreducible test of Q is in K by Section 6 and is therefore ordinarily irreducible. Composing with the original p0 gives the required corrected map Q->C0, with the SAME control selected in Section 1.

Now let S be ANY original exact weak induced subset of Q with |S|<=n. Give S its inherited profile relations. Restrict the ordinary map into P+ to S, and factor through its EXACT induced image in P+, whose cardinality is at most |S| even if the map is noninjective. The relational sparsening theorem gives an ordinary map of that image into a strict B+-tree; Section 3 completes the tree in E+ for finite E in K. Compose and forget profiles.

The resulting positive map of the ORIGINAL weak S into E protects all original closed U-irreducible tests of S: each embeds into Q, hence belongs to K by Section 6, hence is ordinarily irreducible. This is precisely a corrected K-completion of S. No chosen completion of generators is extended to a larger hull, and no size bound is transferred from S to its hull.

## 8. Ramsey transfer does not require every global A-copy to lift

The tagged Ramsey arrow gives a tagged B-copy in Qtag. To recover the original arrow, colour each tagged A-embedding by the colour of its original reduct. Every original embedding A->B lifts to the canonical profile and tagged expansions of the CLOSED INPUTS. Therefore all original A-copies inside the selected B-copy are represented among the tagged A-copies to which monochromaticity applies.

It is unnecessary, and generally false, to require that every original A-copy anywhere in Q lift to a canonical expanded A-copy. Only the closed-input A->B lifting is used in this last argument.

Apply the original fixed-cutoff local-completion axiom at B,C0 to Q, using Sections 6--7, and then the checked B-copywise Ramsey transfer. This is the proposed end of the alternative proof.

## 9. Adversarial checklist and exact formalization boundary

The following shortcuts are deliberately excluded: changing n after selecting an auxiliary control; replacing weak tests by hulls; identifying vertex size with generating rank; inferring original closedness from lifted closedness alone; reusing an old closure symbol for incompatible expanded roots; treating a noninjective root completion as a full boundary embedding; assuming arbitrary weak embeddings extend to closures; claiming that every global original A-copy lifts.

**Implemented, pending the PR's actual CI:** canonical profile representation; closed-range containment; full profile embedding preservation/reflection; lifted Ramsey arrow; transport of records; actual profiles of tuple closures; construction of one common closed K-boundary for a finite weak profile root; hereditary ordinary irreducibility of profiled B.

**Not yet implemented:** Section 3's strict-tree completion induction; the general fresh-symbol tagged language and both local-law transfer lemmas; the final closed sparse pass and original exact weak-test/control-map transfer. These are the concrete remaining declarations for THIS route. No theorem or instance in the repository assumes them implicitly.

The unrestricted coordinated theorem must remain orange until those bridges are actually constructed and the final theorem, with no construction-oracle premise, passes its own axiom audit. The native Lemma 2.30 remains a distinct target even if this alternate main-theorem proof succeeds.
