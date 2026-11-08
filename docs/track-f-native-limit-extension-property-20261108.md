# Track F — exact native Fraïssé extension property from the fair full chain

**8 November 2026.** Independent English proof and adversarial Lean integration plan for the ORIGINAL root-injective global maximal-trace finite age. This is a working mathematical proof, **not** a Lean kernel certificate. The numbered `ramsey.tex` is frozen.

## Exact target and hypotheses

Let `F` be a forbidden family, `K*` its original regular root-injective global maximal-trace finite age, and assume an actual `GlobalOriginalFiniteFraisseInput F`. The package includes finite age nonemptiness, full hereditary embeddings, FULL JEP, FULL strong AP, and genuine finite representatives covering all full-isomorphism types. **For arbitrary reducible connected forbidden families, this input still depends on the unproved `GlobalCanonicalShadowFreeAmalgamation` / original Claim 2.** In the previously verified irreducible-source case it can be constructed without that extra shadow-free premise, given all other hypotheses.

Let `X_n` be the ACTUAL fair chain from merged #928, with full successor maps `s_n:X_n↪X_{n+1}`, full transition maps `e_{m,n}:X_m↪X_n` from #852, and their composition law from merged #857. The finite fair schedule revisits every genuinely finite representative extension diagram at **every sufficiently late stage** (#845).

Let `M` be the decoded native structure on the actual first-order function-graph directed limit (merged #903/#918), and let `u_n:X_n↪M` denote the desired full native canonical embeddings, currently under independent Lean checking in **#919 → #930**.

The target extension property is:

For each finite full age extension `i:A↪B`, each FULL embedding `f:A↪M`, there exists a **FULL** embedding `g:B↪M` such that `g∘i=f`, with equality pointwise on all vertices of A.

This assertion does **not** presume a uniform bound on extension sizes, any one-point-generated closure, function totality, unique outputs, or a weak HE map in place of a FULL functional embedding.

## Ingredient I — transport arbitrary diagrams to the fair schedule

- [#950](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/950) proposes a theorem for ANY finite full embedding `i:A↪B` with B in `K*`: choose genuine representatives `P,Q∈K*` and surjective FULL embeddings `a:P↪A`, `b:Q↪B`, and define the FULL representative extension `d := b⁻¹∘i∘a:P↪Q`. Then **`b∘d = i∘a`**.
- [#952](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/952) proposes full witness transport: if `j_Q:Q↪T` and `f_A:A↪T` are FULL and `j_Q∘d = f_A∘a`, then `g_B := j_Q∘b⁻¹:B↪T` is FULL and `g_B∘i=f_A`. The key equation uses surjectivity of a, injectivity of b, and the genuine complete-fibre-preserving inverse from **merged #931**.
- [#954](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/954) proposes the combined **FINITE-STAGE** extension property: given any current stage X_m, any full `f_m:A↪X_m`, any `i:A↪B` in the original age, choose sufficiently late `n≥m`, then a FULL `g_n:B↪X_{n+1}` with
  `g_n∘i = s_n∘e_{m,n}∘f_m`.

All three PRs are drafts awaiting full Lean CI. Their role is **independent of the limit construction**. The core construction is finite and uses no hidden infinite-model existence assumption.

## Ingredient II — factor any finite FULL root copy in M through one stage

- [#943](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/943) proposes a common-stage theorem for any finite tuple of vertices in the actual first-order direct limit. It produces one n and vertices in X_n mapping to that tuple via `u_n`, using Mathlib's `exists_quotient_mk'_sigma_mk'_eq`.
- [#919](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/919) proposes closedness of every first-order stage embedding in M, by descending a putative new function output to the finite original stage, using merged #901 whole-fibre stability.
- [#930](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/930) proposes converting each first-order stage embedding to a **FULL native-functional embedding** `u_n:X_n↪M`, using the verified closed-graph/full-embedding interface #848.
- [#949](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/949) proposes full finite-stage factorization: for finite A and FULL `f:A↪M`, obtain n and a FULL `f_n:A↪X_n` with `u_n∘f_n=f`. Its crucial output-fibre proof cancels `u_n` only after establishing complete function-value fibre equality, rather than using a merely induced first-order subset.

All four remain under independent full CI. If the common-stage representation exists only as a vertex function and #930 is missing, its factorization is **not** valid as a full functional embedding; this is the primary semantic guardrail.

## Main English proof of finite extension property in M

Let i:A↪B and f:A↪M be arbitrary FULL embeddings with B in K*. Finiteness of A and B is part of their age membership.

1. Apply the verified-once-available factorization theorem #949 to f, obtaining m and full `f_m:A↪X_m` with `u_m(f_m(x))=f(x)` for each x∈A.
2. Apply the finite arbitrary-diagram stage theorem #954 to i, f_m and X_m. Obtain n≥m and a **FULL** `g_n:B↪X_{n+1}` such that for every x∈A,
   `g_n(i(x)) = s_n(e_{m,n}(f_m(x)))`.
3. Set `g := u_{n+1}∘g_n:B↪M`. It is a genuine FULL embedding because both factors are FULL (#930).
4. For every x∈A, use the canonical limit cocone equations (proposed in #919), first for n→n+1 and then for m→n:
   `g(i(x)) = u_{n+1}(s_n(e_{m,n}(f_m(x)))) = u_n(e_{m,n}(f_m(x))) = u_m(f_m(x)) = f(x)`.
5. This proves `g∘i=f`, the FULL finite extension property for the original K*.

The construction works with repeated root inputs and nullary functions. All maps commute in the underlying carriers **and** preserve the ENTIRE original set-valued function fibres. Neither the arbitrary n-indexed first-order graph age nor an extension by a weak positive-only HE map appears in the proof.

## Extension property versus Fraïssé ultrahomogeneity

The finite extension property plus exact finite FULL age equality (proposed in #949) does not automatically yield a formally verified automorphism theorem. A further Lean back-and-forth argument is needed.

Given a finite FULL partial isomorphism `p:A≃B` between finite function-closed substructures of M, enumerate M (countable by #900). Alternately use the extension property to cover the next vertex in each domain and range.

The finite-closure issue is real: in a set-valued functional language, simply adding one vertex to a finite closed subset need not yield a finite closed extension. **The workaround supplied by the chain construction** is to choose a common finite stage containing the old partial image and the new vertex, and then work with the image of an ACTUAL finite FULL stage under `u_n`. Since all canonical stage maps are FULL, their images are finite and function-closed. The partial isomorphism is transported along full finite-age embeddings and then extended by the verified finite extension property. An induction/back-and-forth on alternating finite closed domains gives a total full automorphism. This argument must still be formalized separately.

## Adversarial checklist

- **No loose ages:** first-order induced subsets of function graphs are not automatically function-closed; use the FULL native age.
- **No false colour/Ramsey implication:** the Fraïssé extension property of M is distinct from the original Section 3 ordered Ramsey claim and Track E local completion.
- **No mistaken Claim 2 completion:** nothing above removes `GlobalCanonicalShadowFreeAmalgamation` for reducible forbidden families.
- **Nullary JEP:** exact native JEP is a genuine prerequisite in the language convention allowing nullary relations/functions; see the merged #807 obstruction and manuscript note ATRC-073.
- **Certification:** CI of the current PR head must pass all-module Lean compilation, permitted axioms, active-root/source integrity, and admission scans before green validation marks or theorem-availability claims. As of writing, #919/#930/#941/#943/#949/#950/#952/#954 are pending, not verified.

**Status:** Standalone English proof plan, suitable for the next dedicated Lean module after dependencies pass. The numbered manuscript `ramsey.tex` remains frozen.
