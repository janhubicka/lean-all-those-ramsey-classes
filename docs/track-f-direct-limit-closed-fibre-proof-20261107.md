# Track F — exact function-closedness proof for the Fraïssé direct limit

**7 November 2026.** Source-faithful English proof and Lean integration plan. This is an audited reasoning note, not a proof certificate. The numbered manuscript `ramsey.tex` remains frozen.

## Context and verified inputs

The original **root-injective global maximal-trace** finite age is represented by `GlobalOriginalFiniteFraisseInput F`: nonempty, hereditary, full JEP and strong amalgamation, countably many genuine representatives. In general reducible forbidden families, construction of this input still depends on the original unproved `GlobalCanonicalShadowFreeAmalgamation`. The irreducible-source case supplies it under its actual hypotheses.

Verified Track F finite-stage infrastructure:

- #842 constructed genuine finite maximal-trace stages `X_n` with full successor structural embeddings. #845 constructed fair finite prefixes of representatives and extension diagrams. #825/#836/#841 verified finite extension and cofinality steps.
- #852 constructed full old-to-new maps `e_{m,n}:X_m→X_n` for `m≤n`, with complete function-fibre equality.
- #901 proved the **no-new-output** formula:
  `y∈F^{X_n}(e_{m,n}∘x) ↔ ∃z∈F^{X_m}(x), e_{m,n}(z)=y`.
  It also verified that all old/new relations are reflected exactly.
- #837/#848 constructed the arity-exact function-graph presentation in the **functionless** first-order language. In particular a first-order graph embedding is a full native set-valued functional embedding **if and only if** it has function-closed image (precisely the complete output-fibre closure condition).
- #857 supplies the transition coherence equation `e_{m,k}=e_{n,k}∘e_{m,n}` and was merged only after full CI.

## Current independent PRs and their exact limits

**Updated 8 November 2026 — actual GitHub CI and merge status.**

- [#900](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/900) is **merged after full green CI**. The generic quotient carrier is countable; the transition maps use full-induced injective `Function.Embedding` arrows satisfying the required `FunLike` interface.
- [#916](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/916) is **merged after full green CI**. The exact graph decoder recovers native old/new relation tables and whole set-valued function fibres, including nullaries.
- [#903](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/903) proposes Mathlib's actual FIRST-ORDER directed limit of complete function-graph structures. It remains **draft/unverified**. Its earlier run failed because its historical branch did not contain the already merged first-order graph module; the missing exact main-branch source, axiom audit, and active root have now been copied into the branch, and a fresh CI is pending.
- [#918](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/918) proposes decoding the entire first-order limit as a genuine native functional STRUCTURE, but not full embeddings; it remains draft/unverified, stacked on #903, with the same missing-source repair.
- [#919](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/919) proposes the crucial exact function-CLOSEDNESS of every canonical finite stage in the decoded limit using the merged #901 no-new-output theorem. It remains draft/unverified, stacked on #918.
- [#930](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/930) proposes the next theorem: reconstruct genuinely FULL native finite-stage embeddings from #919's closedness and the merged #848 full/closed graph bridge. It remains draft/unverified, stacked on #919.
- [#928](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/928) proposes a concrete fair finite chain and a repeated extension-request invariant. [#931](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/931) proposes inversion of surjective FULL functional embeddings, and [#932](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/932) combines both to cover every finite age member. All three remain draft/unverified.

**Important:** None of the pending PRs is to be treated as a Lean-verified theorem until its own current-head all-module, axiom, source-integrity, and admission checks pass. The genuine native limit's age equality, finite extension property, back-and-forth ultrahomogeneity, and unrestricted reducible-source shadow avoidance remain separate obligations.

## The missing closed-image theorem — fully explicit English proof

Fix a finite stage `X_m` and its canonical first-order embedding
`u_m : X_m.graph ↪ D` into the directed-limit graph structure `D`.
Set `M := Structure.ofGraph(firstOrderRelGraphDecode D)`.

**Claim.** For each native old/set-valued function symbol `S`, each input tuple `x : Fin(arity(S))→X_m`, and each `y∈M` satisfying
`y∈S^M(u_m∘x)`, there exists `z∈S^{X_m}(x)` with `u_m(z)=y`.

1. Because every vertex of the first-order direct limit is represented by a stage vertex, write `y=u_i(t)` for some stage `i` and vertex `t∈X_i`. This is `FirstOrder.Language.DirectLimit.exists_of`.
2. Choose a stage `k≥m,i` (for natural indices take `k=max m i`). The coherent canonical inclusions satisfy
   `u_m = u_k ∘ e_{m,k}` and `u_i = u_k ∘ e_{i,k}`; this is `FirstOrder.Language.DirectLimit.of_f`.
3. Put `x_k=e_{m,k}∘x` and `t_k=e_{i,k}(t)`. By the definition of `M` and the exact graph decoder (#916), the assumption is the first-order truth of the `(arity(S)+1)`-ary graph-relation symbol at `(u_k∘x_k,u_k(t_k))`.
4. The canonical first-order map `u_k` is a **relational embedding**, so it reflects that graph relation. Consequently `t_k∈S^{X_k}(x_k)` (use #837's function-graph incidence equivalence).
5. By #901's no-new-output equivalence for the **full** finite transition `e_{m,k}`, obtain `z∈S^{X_m}(x)` with `e_{m,k}(z)=t_k`.
6. By coherence, `u_m(z)=u_k(e_{m,k}(z))=u_k(t_k)=y`, as required.

This argument also handles **arity zero**: the input tuple is uniquely empty, and the common-stage computation still includes the output vertex. It does not require function totality, uniqueness of outputs, bounded root widths, or finite forbidden families. It proves closure for *every* native function symbol, including all old partial/set-valued ones, and all information is transported through genuinely full finite-stage embeddings.

**Consequence.** The canonical graph embedding `u_m` has `Structure.ClosedMap X_m M u_m`. Apply the existing #848 `firstOrderNativeGraphEmbedding_toFull` theorem to obtain a **genuine full native functional embedding** `X_m ↪ M`. This includes equality of complete whole output sets, not merely preservation of positive function incidences.

The corresponding *relational* reflection follows directly from Mathlib's first-order canonical embedding; no extra closure argument is needed for old or newly-added piece-class relation symbols.

## Remaining proof obligations, in correct order

1. Compile #900 with genuinely `FunLike` transition arrows (and explicit countability of the quotient). Compile #903 with the correct first-order stage structures and a coherent first-order directed system; never assume these are automatically present merely because the underlying carriers have a quotient.
2. Merge #916's graph decoder only after full CI and its exact whole-fibre iff checks.
3. Formalize the six-step closedness argument above, using `DirectLimit.exists_of`, `DirectLimit.of_f`, `relMap_quotient_mk'_sigma_mk'`, and #901. This is the FIRST missing theorem for the completed native limit.
4. Prove the finite-full-age equality: every actual finite age object embeds into `M` by cofinality and full stage inclusions; conversely any finite full substructure in `M` factors into a finite full stage, by choosing a common stage for its finitely many vertices and using full image closure.
5. Use the fair schedules (#845) and finite stage demand lemma (#841/#842) to prove the finite extension property for `M`. The recurrence of a diagram is essential because a full root copy may appear only at a later stage.
6. Derive ultrahomogeneity by back-and-forth over finite **function-closed** substructures. Every finite vertex tuple sits in one finite full stage, hence has finite native closure.
7. Keep the original Ramsey transfer, exact shadow-free amalgamation for unrestricted reducible families, universality/existential completeness of the native reduct, and model-theoretic `ω`-categoricity as DISTINCT tasks. In particular, finite labelled-carrier tables alone do not imply oligomorphicity for arbitrary functional reducts.

## Adversarial warnings

- A bare first-order induced subset of the function-graph language need **not** be function-closed; using the first-order age without this extra condition would be unsound for the native paper.
- Mathlib's first-order Fraïssé file does **not** automatically provide its own fully formalized limit existence theorem. The explicit direct-limit construction and finite extension property are being developed for precisely that reason.
- The old nullary-JEP obstruction is certified by #807 and recorded as ATRC-073. Old-symbol positive arity is sufficient for JEP in the connected-source case but not necessary; use the exact native full JEP condition.
- A `#print axioms` certificate verifies a theorem WITH its hypotheses. A conditional finite-age input does not discharge the published general connected reducible-source Claim 2/shadow-avoidance step.

**Status: English proof plan; no new Lean validation mark until the exact closedness and limit statements compile with the full all-module/axiom/admission CI gate.**
