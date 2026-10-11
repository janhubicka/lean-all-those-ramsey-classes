# Published 2019 validation ledger

Repository initialized 10 October 2026. All claims below refer to the
*published* 2019 article and imported `partite-construction` at
`23c09415f7bae6b0099c9d986719ae1eb2678b0d`. The first complete local
build/axiom audit succeeded and was squash-merged at
`0645ccbdd1e77e40efe1e082913240b75c437a71` (PR #1).
Evidence goes here, never into the published LaTeX text.

| Paper | Declared Lean source | Status |
|---|---|---|
| Definition 2.12 | `ClosureDescription2019.lean` `ClosureRule` | BLUE: representation |
| Definition 2.13 | `ClosureDescription2019.lean` `IsUClosed` | BLUE: representation |
| Definition 2.15 | `ClosureUIrreducible2019.lean` | BLUE: exact *literal* interface |
| Definition 2.17(4) | `LiteralLocalFiniteness.lean` | GREEN (local PR #1): exact printed local implication at n=1 for all classes without singletons; paired-class instance |
| Theorem 2.18 | `Theorem218Counterexample.lean`, `PairedStrongAmalgamation.lean` | **GREEN NEGATIVE THEOREM** (PR #56): unconditional Lean proofs of `¬ LiteralTheorem218Target` and `¬ CorrectedTheorem218Target` for the (4b)-only repair; does NOT address proposed coordinated repair |
| Theorem 2.19 | `AllThosePartialFiniteModels.lean` | GREEN upstream: original partial single-valued functions, all arities |
| Definition 2.22 / Lemma 2.23(1) | `ClosureDescription2019.lean` | GREEN upstream |
| Minimal (4b)-only local condition | `CorrectedSingletonEscapeBound.lean`, `Corrected4bLocalCounterexample.lean` | GREEN PR #38: n(B,C0)=|C0|+1 works for every B∈K; combined with GREEN strong AP #49 yields certified refutation of the (4b)-only theorem in #56 |
| Lemma 2.23(2) | `ClosureFreeAmalgamCompletion.lean` | GREEN upstream for U-closed sides/overlap; editorial TODO removes undefined strong-completion clause |
| Definition 2.24 | `ClosureSemiClosed2019.lean` | BLUE: representation with checked partial lemmas |
| Definition 2.25 | `ClosureUSize2019.lean` | BLUE/PARTIAL; possible printed ambiguity recorded in TODO |
| Lemmas 2.27–2.28 | Native closed/semi-closed partite modules | PARTIAL: published weak intrinsic test statements not fully checked |
| Lemma 2.29 | `Lemma229Counterexample.lean` | **REFUTED LITERALLY (GREEN negative proof)**: explicit A,B,C0 satisfy hypotheses but no C has all intrinsically U-irreducibles covered; closed-test repair pending |
| Lemma 2.31 / Definition 2.17(4c) | `LiteralWeakRankBridge.lean` | GREEN conditional: closed rank control by fully protected original-style maps yields ALL exact weak n-vertex completions; supplying those maps remains open |
| Lemmas 2.30–2.31 | Closure rank/relative boundary modules | OPEN for the general corrected higher-rank iteration |
| Paired-equivalence counterexample | `PairedEquivalences.lean`, `FinitePairedClass.lean`, `PairedStrongAmalgamation.lean`, `Theorem218Counterexample.lean` | **GREEN:** all class premises, exact finite strong amalgamation on the vertex pushout (#49), both final negative theorems (#56); persistent non-Ramsey colouring |
| Coordinated repair: excluding paired K by all-cutoff cycles | `CoordinatedCycleBlocks.lean`, `CoordinatedCycleSmallTests.lean`, `CoordinatedCycleGadgetWitness.lean`, `CoordinatedCycleControlHom.lean`, `CoordinatedCycleZeroRegression.lean`, `CoordinatedCycleGadgetPositions.lean` | **ORANGE:** Green uniform finite C_k, U-closure (#59), complete *positive* C_k→C0 homomorphism (#60), exact weak missing-block bound (#55), uniform three-block incidence (#62), finite k=0 Lean regression and independent 309,136 weak-subset regression (#61). Induced B0 gadget copies, all protected closed tests, exact weak-test K completions, and general coordinated Ramsey theorem remain open |

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

## Local CI proof certificate

Merge commit `0645ccbdd1e77e40efe1e082913240b75c437a71` records
successful GitHub Actions run `38060912578`: 3,303 build jobs; 17
individually audited declarations with only standard logical axioms;
finite regression on 1,658 structures / 25,827 closed test subsets /
85 B embeddings all passing.

Further immutable proof commits and successful full CI runs:
- PR #2 `ab09b221adad2f44fdcd9f854419726310e265f1`: concrete matching closure
- PR #3 `c173bc633eab93ca18ba33b5a917fee25b967ffa` (CI `38073880406`): finite K and closed hereditariness
- PR #5 `69477b78f3f6cbf954e44a2544bf78510b3080e0` (CI `38074200658`): matching closure preserved in free amalgam
- PR #7 `83bc0296ae55664d4c88e38a8954f090795284b2` (CI `38074486260`): one-clause repaired (4b) with literal 2019 map and weak-test semantics
- PR #8 `fbe0c5f4036386bf1e79f7c8dcfe721729d0f70f` (CI `38074932974`): exact weak-test rank bridge under fully protected maps
- PR #9 `11180c7e8fcf5981b9cbc480a6b300cf63952d93` (CI `38075158171`): bounded strong amalgamation regression on 72,839 spans; NOT a Lean proof
- PR #10 `f1ce1f5be6777c8ee02b4c831c53801741397e85` (CI `38075422312`): direct Lean witness refuting printed Lemma 2.29

PR #38, merge `3e535634d662f7a984fd687c352a64a8606a639a` (CI `38083046493`), established the (4b)-only local axiom automatically at cutoff `Nat.card P + 1`. **That result is no longer conditional at the theorem level.**

Latest checkpoint (11 October 2026):
- PR #48 merge `94f27c6db3d2cad64fcb14e59835fdd6bd7acbba`: exact induced E extension plus common order on the free pushout, with green CI.
- PR #49 merge `738293798cb0eb384cadcf9e6cee3b06c7ec290d`, successful CI `38111771221`: **general Lean strong amalgamation theorem** for finite ordered paired equivalences, with permitted-axiom audit; finite regression still independent.
- PR #56 merge `514fac46606dab914b4cfa2425a5af155130b451`, successful CI `38111968393`: both unconditional theorem-level negative results and their permitted-axiom audits.
- PRs #54 and #55, green CI `38111850367`, `38111852226`: unbounded long-cycle matching-block carriers, fixed-control projections and the cardinal lemma showing every exact weak `n`-vertex test misses at least one backbone block. These are **components only**, not an all-cutoff witness satisfying (4a)-(4c).
- PR #58, CI `38136414700`: matching-closure criterion without E transitivity or total order, merged.
- PR #59, CI `38136868482`: genuine uniform U-closed partial relational E-cycle C_k, merged.
- PR #60, CI `38136871704`: full positive control homomorphism C_k→C0 (all three symbols), merged.
- PR #61, CI `38137484538`: Lean finite five-block nontransitivity/path check plus separate exhaustive bounded regression of 309,136 exact weak vertex subsets, merged. This is not a proof for arbitrary k.
- PR #62, CI `38136962007`: uniform path/closing gadget block incidence and distinctness, merged.

No green theorem asserting that the coordinated Definition 2.15-map/Definition 2.17(4b) repair is correct exists. Actual uniform C_k relational witnesses and their positive projection are now Green, but the **closed-test** embedding condition (4a), membership coverage (4b), and exact small-test K-completions (4c) remain unproved. PRs #64–#67 develop separable label/profile, induced-template and closed-test reduction stages; do not mark their statements verified before CI and axiom audits succeed.

The complete general higher-rank multiamalgamation theorem under any alternative repair remains unverified. Do not promote partial closed-test Picture machinery or a different completion-map convention to a green theorem-level marker; keep the published prose frozen pending formal proof and editorial review.
