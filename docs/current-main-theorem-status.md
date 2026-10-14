# Current main-theorem status — 13 October 2026

## Verdict

**The unrestricted coordinated corrected RELATIONAL closure-description Ramsey theorem is proved, fully CI-verified, and merged.**

The endpoint is `AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening` in `AllThoseRamseyClasses/Published/Coordinated2019ProfileSparseWitness.lean`. It constructs the sparse witness rather than taking it as a premise. There is no native rank-increment or compatible-boundary constructor hypothesis, and no restriction on the local cutoff n(B,C0).

PR **#195**, proof head `c783c23377d56d29bdfb7d61fe95e9c7e96073d2`, passed complete GitHub Actions run **38479503776**, job **115578421589**. All project modules, the permitted-axiom checks, the three finite regressions, and the admission scan passed. The run finished at 22:51:57 UTC on 13 October 2026. The final declarations were originally audited in `CheckAxiomsCoordinated2019ProfileMain.lean` and are now in `CheckAxiomsStructuralCore.lean` plus `CheckAxioms.lean`; only `propext`, `Classical.choice`, and `Quot.sound` are permitted. PR #195 was squash-merged as **`f88ce3113076f348a06906c0e2cf6e12b47c985d`**.

The fresh-tag dependency **#194**, head `34b8208782134db0e6ea38902df90ce34f010d5a`, independently passed complete run **38479196563**, job **115577338249**, and was merged first as `23ffded78eab0d9e8ce3fa03c9bc1e2f41f83817`.

Verification was performed in GitHub Actions, not by a local Lean installation. The initial failure of the final wrapper was a colour-universe mismatch; the checked fix changes its binder from `κ : Type*` to the pre-existing exact contract's `κ : Type`, without changing any mathematical class or local-completion hypothesis.

## Exactly what is proved

```lean
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness

-- Namespace: AllThoseRamseyClasses.Published
-- Relational language L, with the established explicit class interface:
coordinated2019_ramsey_by_profile_sparsening
  (R K : StructureClass (L := L))
  (rules : ClosureDescription L)
  (hR : FiniteRamseyClass R)
  (hRIrred : ∀ C, R C → C.Irreducible)
  (hK : IsCoordinated2019MultiamalgamationClass R K rules)
  : FiniteRamseyClass K
```

The displayed signature abbreviates the carrier/universe binders; consult the cited source for the exact declaration. `IsCoordinated2019MultiamalgamationClass` retains explicit isomorphism invariance and the previously established exact induced-test conditions. The theorem is not being asserted for arbitrary non-isomorphism-invariant predicates.

The two coordinated definition repairs remain exactly as agreed: Definition 2.15 protects induced source tests which are BOTH intrinsically U-closed and U-irreducible, and Definition 2.17(4b) tests membership on those same structures. Intrinsic U-irreducibility is unchanged. Clause (4c) still quantifies over ALL original exact weak induced subsets with at most the fixed n(B,C0) vertices. The original Ramsey control may be nonclosed. No extra root, rank, sparsity, or completion assumption was added to the final class interface.

This closes the corrected **relational closure-description main theorem**. It certifies the revised relational formulation, not the earlier printed definitions, every remaining result in the paper, or a primitive-function formulation without its explicit relationalization bridge. This is a statement about the scope of certification rather than a verdict on the earlier text. The original native Lemma 2.30 generating-rank statement remains separate and unproved by this route.

## How the construction closes the gap

The complete English proof and semantic audit are in [coordinated-profile-proof-20261013.md](coordinated-profile-proof-20261013.md).

1. Fix the original Ramsey control C0 and n(B,C0); use the constructed corrected Lemma 2.28 to obtain a closed Ramsey Picture D over C0.
2. Expand by generated-closure profiles: each record names an actual closed substructure of the fixed B and a generating tuple. Full embeddings of closed structures lift with full reflection. Apply the existing purely relational strict-tree sparsening theorem to the profiled inputs at n.
3. Complete strict trees of profiled B-copies in K. A shared weak profile root determines ONE actual closed K-boundary with compatible FULL embeddings into both targets. These boundaries are constructed, not assumed.
4. Introduce a distinct fresh closure symbol for every compatible full expanded root pattern, and apply the unrestricted closed Picture theorem once more. Derive BOTH tag normality and original-root validity from actual closed-irreducible B-copy coverage. Recover original closedness and original closed-irreducible coverage.
5. For every original weak S with |S|<=n, use its exact image of size at most |S| in the sparse profile structure. Compose the ordinary maps through a strict profile tree into a genuine finite K-target. Original closed-test coverage turns the resulting ordinary map into the exact corrected protected map on S.
6. Forget the auxiliary arrow, compose back to the SAME C0, and apply the SAME fixed-cutoff local axiom and B-copywise Ramsey transfer.

The auxiliary profile language permits all finite tuple lengths and need not have finitely many symbols. The construction theorems invoked allow such signatures. This is an alternative proof rather than a claim that the old cut automatically has small projected ranks.

## Verification map

| Component | Source / declaration | Status |
| --- | --- | --- |
| Unrestricted initial closed Picture | `InducedClosed2019UnrestrictedInitial.lean` | Previously verified, reused twice in the appropriate languages |
| Canonical profiles and generated-range reflection | `GeneratedClosureProfiles2019.lean` | Verified; included in final dependency audit |
| Actual closed boundary from shared weak profile | `GeneratedClosureProfileBoundary2019.lean` | Verified; no boundary oracle |
| Finite K-completion of strict profile trees | `ProfileStrictTreeCompletion2019.lean` | Verified; actual strong amalgamations |
| Fresh tag rules, both local laws, original reduct transfer | `ProfileRootTagLanguage2019.lean`, `ProfileRootTagClosedness2019.lean`, `ProfileRootTagLocalLaws2019.lean`, `ProfileRootTagTransfer2019.lean` | #194 complete CI 38479196563; also included in #195 audit |
| Sparse witness for EVERY fixed exact weak cutoff | `coordinated2019_profile_sparse_witness` | #195 complete CI 38479503776 |
| Corrected relational main theorem | `coordinated2019_ramsey_by_profile_sparsening` | #195 complete CI 38479503776 |
| Native closed generating-rank increment | `Proposed2019RankIncrementStep` | Not proved; no longer a premise of the alternative endpoint |

## What remains separate

The old conditional interfaces `coordinated2019_ramsey_of_two_picture_constructors` and `coordinated2019_ramsey_of_higher_rank_constructor` are historical alternative proof contracts. Their unproved native constructor is not a remaining dependency of the new theorem.

For that original rank argument, the outstanding proof obligations concerning free covers of transverse copy ranges and separator costs still require justification. A possibly noninjective protected root completion is not a pair of compatible full boundary embeddings. These objections must not be erased or promoted to green simply because the alternative proof now succeeds.

A primitive-function version of the manuscript theorem needs its relationalization hypotheses and transfer to be explicitly connected to the corrected relational statement. The final declaration above does not itself perform that transfer. Other numbered results retain their individual validation status. Replacing the original printed proof by the profile proof is an editorial decision; the new proof is supplied separately in the review TeX, without modifying the numbered mathematical prose.
