# Track F: adversarial Section 3 theorem-assembly crosswalk (1 November 2026)

**Scope:** the original distinct-root global canonical piece expansion in the
2019 `ramsey.tex`, specifically `mainthm` and the later Ramsey-lift
`thm:main`. This is **not** the verified corrected relational Theorem 2.18,
and **not** the auxiliary folded/all-components finite-family lift.

## Printed statement versus independently verified code

| Paper assertion | Existing proof or Track F endpoint | Status and additional hypotheses |
| --- | --- | --- |
| `mainthm`: finite maximal lift age is hereditary | `IsGlobalFiniteMaximalTrace.of_embedding` | Proven for **full** embeddings, including complete old function fibres |
| Finite original forbidden-free structures have an expanded age member; exact reduct | `globalOriginalMaximalTrace_exactReduct` (new assembly of `globalFiniteMaximalTraceAge_exact_reduct` and native `avoidsGlobalFunctionalEHN_of_embedding`) | Proven assuming regularity; no shadow-avoidance or Claim 2 needed |
| Regularity gives precompactness up to full isomorphism | `globalMaximalTraceAge_finiteIsoRepresentatives` | Proven for the actual hereditary maximal-trace age; assumes regularity |
| `mainthm`: finite maximal lift age has JEP | `globalMaximalTraceAge_JEP_connected_positiveArity` | Proven for connected nonempty sources when **all old relation and function arities are positive**; `globalMaximalTraceAge_JEP_connected_of_emptyRoots` is the version for nullary symbols with compatible full empty roots |
| `mainthm`: finite maximal lift age has strong AP | `globalFiniteMaximalTraceAge_strongAmalgamation_of_shadowFree`; Track F `globalFiniteMaximalTrace_fraisseCore_of_shadowFree` | Proved **only if** `GlobalCanonicalShadowFreeAmalgamation` is supplied; this is exactly the missing unrestricted combinatorial theorem |
| Specific stronger conditions suffice for strong AP | `globalOriginalMaximalTrace_fraisseCore_of_geometricConditions` | Additional `GlobalMinimalWitnessGeometricConditions` includes input-pair coverage and both exact source-boundary conditions; **not** derived from printed hypotheses |
| Irreducible-source special case of strong AP | `globalOriginalMaximalTrace_fraisseCore_irreducible` | Proven for the narrower irreducible forbidden-source class; NOT the arbitrary reducible-source theorem |
| Strong amalgam shadows are native **free** amalgams | Existing construction works via true free old-witness amalgams, but Track F's public class record asserts only full strong AP | Separate exact source-to-paper bridge: do not promote a mere exact-overlap record to a theorem that the requested shadows themselves are the prescribed free amalgam |
| `mainthm`: Fraisse limit exists when age countable | No generic countable-limit construction in this Track F module | HP/JEP/AP must be combined with **countability up to isomorphism** and an appropriate nonempty-age hypothesis; we do not claim an infinite limit |
| `mainthm`: finite relational regular case gives omega-categorical existentially complete universal shadow | No complete Lean proof | Needs the Fraisse limit and additional genuine model-theoretic/saturation/universality arguments |
| `thm:main`: ordered maximal lifts form a Ramsey class | No complete Lean proof | Requires the remaining unrestricted Section 3 shadow-avoidance and a correct application of the local completion/partite Ramsey theorem, plus all expanded-type Ramsey arrows; Track F proves only `globalMaximalTrace_expandedArrow_controls_shadowColor_oneType`, which is **typewise**, not class-level |

## Important quantified distinctions

1. `GlobalCanonicalShadowFreeAmalgamation F K` quantifies over
   **actual full native functional free-amalgam diagrams** and requires
   equality of **all original root-injective** canonical piece labels
   on the common full old-language root. It is not a theorem from
   regularity or EHN image closure.
2. `GlobalMinimalWitnessGeometricConditions F` quantifies over
   genuinely support-minimal forbidden EHN witnesses in every such
   diagram. It asks for irreducible input-test pair coverage and
   complete **two-sided generated boundaries**; these are extra
   assumptions. They do not follow from the source-only first-inner-root
   safe-path lemma.
3. A full expanded embedding gives a full old-shadow embedding, but
   **not every** old-shadow embedding is an embedding of a fixed
   expansion type. The one-type Ramsey-arrow lemma therefore makes
   no claim about all old-coloured A-copies.
4. Full JEP is not automatic in native languages with nullary data.
   If the paper's convention allows a nullary relation `R`, take
   `F = ∅` and two finite one-vertex native structures with
   `R` true and false respectively. The empty family is regular and
   image-closed, yet no structure admits full embeddings of both:
   reflection of the nullary truth value contradicts itself.
   The same issue applies to incompatible nullary function fibres.
   Either the language convention excludes such symbols, or the
   printed JEP line needs a compatibility qualification. This is
   the independent **ATRC-072** audit issue, not a flaw in the
   positive-arity JEP theorem.

## Track separation

- **A** supplies the missing actual transported outer-component geometry.
- **B** supplies arbitrary rooted incompatibility-context/profile transport.
- **C** proves iterated local B-source descent and the eventual Claim 2 contradiction.
- **D** resolves noninjective weak root images for the *original* distinct-root lift.
- **E** supplies genuine finite-family Ramsey transfer/ordered Ramsey theorem.
- **F** assembles only established implications, checks the exact final
  quantifiers and audited kernel signatures, and refuses to mark
  `mainthm` or `thm:main` green until the dependencies are discharged.

**Manuscript policy:** `ramsey.tex` is frozen. Review-only TODO
entries `ATRC-068`--`ATRC-071` remain open; `ATRC-072`
identifies the separate nullary JEP issue. This file does not silently
edit the original numbered prose.

**Verification policy:** `CheckAxiomsGlobalOriginalSection3ClassAssembly.lean`
and `scripts/active_roots/GlobalOriginalSection3ClassAssembly.txt` protect
the new Track F declarations. Treat them as *proposed* until the PR's
full all-module Lean/axiom/admission CI succeeds; a named-axiom check
certifies the theorem INCLUDING its hypotheses and is never a proof
that its assumptions hold.
