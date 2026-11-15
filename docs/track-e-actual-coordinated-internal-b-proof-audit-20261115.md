# Track E — actual coordinated 2019 internal B-extension, English proof and adversarial boundary

**15 November 2026.** This is a proof audit for the *relational* two-pass 2019 sparsening theorem, not an amendment of the frozen survey TeX. The proposed Lean endpoint is `coordinated2019_profile_sparse_witness_with_INTERNAL_B_coverage` in PR #1212, stacked on #1211 and #1210 and pinned to local closed-root saturation #698. All stacked proofs remain conditional on green exact-head Lean and standard-axiom audits.

## Original statement: no added hypotheses

Let `A,B` be `U`-closed finite structures in an arbitrary relational language, with `B∈K`, and let `K` be closed-`U` hereditary with finite strong amalgamation, every `K`-member `U`-closed and ordinarily irreducible. Fix *the original* `C₀`, a Ramsey arrow `C₀→(B)^A_κ`, and an arbitrary finite small-test cutoff `n`. The existing coordinated theorem constructs `Q_old` with a protected original control, full Ramsey arrow, external closed-`U` irreducible `B`-test coverage, and exact induced weak-`K` completions for every `S` of size ≤ `n`. We propose to retain **all** these clauses while also establishing *internal* `IrreduciblesExtendTo B Q_old`.

### 1. Two already constructed intermediate stages

The unrestricted initial Ramsey Picture yields `D` over the unchanged original `C₀`. Expand `A,B,D` by genuine generated closure profiles. Strict **relational** sparsening of the expanded structures yields `P`, not just a Ramsey arrow and strict local `Bplus`-tree completions of all ≤`n` tests, but also the genuine internal-`Bplus` extension certificate `hPExt`. The latter was previously returned by the strict theorem but discarded in the coordinated proof under the name `_hPExt`. No new abstract coverage oracle is needed.

Canonical fresh root tagging yields `Atag, Btag, Ptag`. The existing second unrestricted tagged Ramsey pass constructs the *actual* `Q`, `U`-closed in the fresh-root-tagged language with protected external `Btag`-test coverage, the Ramsey arrow `Atag→(Btag)_κ^...Q` and the selected ordinary full-test homomorphism-embedding `q : Q→Ptag`.

The new independent upstream theorem in #1170 proves that `hPExt` transfers to **internal Btag-extension of Ptag** on the exact tagged control carrier, and that `Btag` is ordinarily *hereditarily irreducible*. Both use only the canonical Ptag/Btag definitions; **Q itself is never assumed canonical**.

### 2. One selected-map-compatible closed-root Btag attachment

Choose an ordinary irreducible exact seed `S` in the current tagged source `Qcur`. Its ambient `U`-closure `H=cl_U^Qcur(S)` is `U`-closed and `U`-irreducible by the already verified closure-hull theorem. Protected external test coverage embeds **that exact H** fully into `Btag`; hereditary ordinary irreducibility of `Btag` makes `H` ordinarily irreducible too. The existing selected homomorphism-embedding maps `H` fully into `Ptag`. Internal `Btag`-coverage of `Ptag` therefore provides a full `β:Btag→Ptag` containing **the selected q[H]**. Factoring this selected full H-image through β constructs the required `j:H→Btag` with `β∘j=q|H`; it is not the unrelated external embedding `H→Btag`.

Free-amalgamate a fresh Btag-copy to Qcur over H. Because **H itself is U-closed**, the verified relational free-amalgam closure theorem preserves `U`-closedness of the new source. Because the two maps to the same Ptag agree on H, the verified free-amalgam fold preserves the original selected homomorphism-embedding, with equality on every old vertex. Because the common root is U-closed, every newly protected closed U-irreducible test factors through one side, preserving **external Btag test coverage**. Every old full Btag copy remains full after the attachment.

The hull H appears only as a *final Btag-attachment boundary*; it is never substituted for any cutoff test S in the weak completion statement.

### 3. Finite saturation and internal coverage

Process the finite powerset of the *original* Q vertex carrier. Whenever the current embedded image of a seed is ordinarily irreducible, perform the operation above; otherwise skip. Retain the certified finite induction state: U-closed source; protected external Btag coverage; same selected HE to Ptag; original core embedding; and every irreducible current test either inside that core or already inside an attached Btag copy. Newly attached sources are free amalgams, so the last localization invariant is the checked `FinalCompletion.CoreOrBase` free-amalgam consequence. At the end every original irreducible seed is now inside a real Btag copy. Every final irreducible either lies in one such seed in the old core or within a previously attached Btag copy. This is **internal** `IrreduciblesExtendTo Btag Qnew`, on ONE finite new source `Qnew`.

The full tagged Ramsey arrow survives along the original full embedding `Q↪Qnew`. The selected map `qNew : Qnew→Ptag` is a homomorphism-embedding, with `qNew∘j=q` on all of old Q.

### 4. Reconstruct (do not inherit) exact small K-completions

A naive argument that every ≤n weak test remains K-completable after adding fresh vertices is invalid. But the original coordinated proof only requires (i) **the strict local Bplus-tree completions of the unchanged P**, (ii) **the selected ordinary HE Qnew→Ptag**, and (iii) **external protected Btag tests of Qnew**. These were preserved above.

For any *literal exact* `S⊆Qnew` of size ≤n, take its selected image `T=qNew[S]⊆P`. Then `|T|≤|S|≤n`. The original strict local tree of the first-stage `P` on T yields a `Bplus`-tree completion. Compose with the selected homomorphism-embedding of the induced profile reduct of Qnew|S to P|T; by the verified profile strict-tree-to-K transfer, obtain a suitable original-language K-target and map on **S itself**. Protected external Btag test coverage upgrades that ordinary map to the corrected induced-closed U-homomorphism-embedding on S. This is the new **kernel-verified upstream #1171** reconstruction theorem. There is no additional weak-test generator or rank bound.

### 5. Forget tags to recover ALL final original clauses

The verified local tag-normality/root-validity argument descends U-closedness and external Btag test coverage from Qnew to its original language reduct `Qold`. Internal Btag copies of Qnew descend to **actual internal B copies of Qold on precisely the same final vertex set** (#1210 candidate). Compose selected ordinary HE through `P→Dplus→D→C₀` exactly as in the already verified original coordinated theorem; use original B-coverage and K-hereditariness to promote this original ordinary HE to the original corrected induced-closed U-protected HE into the SAME C₀.

Therefore, conditionally on the new local finite closed-root saturation and tagged-to-original descent passing Lean, `Qold` simultaneously has all original corrected 2019 relational clauses **plus internal B-extension**, with no added class assumption and the same arbitrary `n`.

## Adversarial checklist

- **U-closedness of common roots is essential.** Ordinary irreducibility alone is insufficient for closure-preserving attachments.
- **Selected-map factorization is essential.** A free external `H→Btag` embedding cannot be used to fold the ORIGINAL selected control HE unless its β-image agrees with the original projected H.
- **The first P already has internal Bplus coverage.** The relevant extra selected-image premise is actually constructed, not assumed. Without P's internal coverage, even a Ramsey arrow, selected HE and external test coverage do not yield source internal B-extension (the independent six-vertex finite regression).
- **No naive locality inheritance.** The original small-K completions must be RECONSTRUCTED after padding as in step 4, not simply reused across free attachments.
- **No replacement of original weak-test carrier.** Hulls are attachment roots only.
- **Still relational.** This is not the historically false all-tuple full-fibre functional projection, and does not certify strict full-native B-trees, general exact clipping/defined-empty weak test equivalence, or class membership of an arbitrary decoded final native H-witness.
- **Pending CI.** #698 / #1210 / #1211 / #1212 must be tested on exact heads and merged in dependency order. No green manuscript validation marker is justified until then.
