# Published 2019 validation ledger

Repository initialized 10 October 2026. All claims below refer to the
*published* 2019 article and imported `partite-construction` at
`23c09415f7bae6b0099c9d986719ae1eb2678b0d`. Updated evidence goes to this file, never to the
published LaTeX text.

| Paper | Declared Lean source | Status |
|---|---|---|
| Definition 2.12 | `ClosureDescription2019.lean` `ClosureRule` | BLUE: representation |
| Definition 2.13 | `ClosureDescription2019.lean` `IsUClosed` | BLUE: representation |
| Definition 2.15 | `ClosureUIrreducible2019.lean` | BLUE: exact *literal* interface |
| Definition 2.17(4) | `LiteralLocalFiniteness.lean` | PENDING CI: full literal local implication holds at n=1 for no-singleton classes; paired-class instance included |
| Theorem 2.18 | `ClosureClosedLocalFiniteness.lean`, `ClosureProtectedPass.lean` | **NOT VERIFIED**; literal wording has a counterexample; repaired higher-rank proof remains open |
| Theorem 2.19 | `AllThosePartialFiniteModels.lean` | GREEN upstream: original partial single-valued functions, all arities |
| Definition 2.22 / Lemma 2.23(1) | `ClosureDescription2019.lean` | GREEN upstream |
| Lemma 2.23(2) | `ClosureFreeAmalgam.lean` | GREEN upstream for U-closed sides/overlap; editorial TODO removes undefined strong-completion clause |
| Definition 2.24 | `ClosureSemiClosed2019.lean` | BLUE: representation with checked partial lemmas |
| Definition 2.25 | `ClosureUSize2019.lean` | BLUE/PARTIAL; possible printed ambiguity recorded in TODO |
| Lemmas 2.27–2.29 | Native closed/semi-closed partite modules | PARTIAL, no claim of full corrected paper statements |
| Lemma 2.31 / Definition 2.17(4c) | `ClosureUSize2019.lean`, `ClosureClosedCompletionRank.lean` | PARTIAL: the exact weak-test bridge is needed; source quantifiers differ |
| Lemmas 2.30–2.31 | Closure rank/relative boundary modules | OPEN for the general corrected higher-rank iteration |
| Explicit non-Ramsey counterexample | `PairedEquivalences.lean` | ORANGE until this repo's build/axiom audit; class-level assembly OPEN |

## Meaning of markers

Exactly as `validation.tex` in the survey:
**GREEN** = the exact scope of the manuscript statement is Lean checked and
the immutable source commit has a successful permitted-axiom audit;
**ORANGE** = only a proof component; **BLUE** = semantic representation;
**TODO** = exact suggested text correction or missing proof. Build failures
must not be recorded as theorem failures or green proofs.

For the paired-equivalence obstruction the uploaded independent mathematical
note is `literal-2019-counterexample.pdf`. The prior finite regression
numbers are NOT verified by this repository unless reproduced.
