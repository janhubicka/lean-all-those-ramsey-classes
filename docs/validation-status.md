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
| Theorem 2.18 | `MinimalRepair4b.lean`, `LiteralWeakRankBridge.lean`, `CorrectedMainTheoremContract.lean` | **NOT VERIFIED**: exact one-clause (4b) target and conditional endgame, but full higher-rank witness still open; published literal theorem refuted |
| Theorem 2.19 | `AllThosePartialFiniteModels.lean` | GREEN upstream: original partial single-valued functions, all arities |
| Definition 2.22 / Lemma 2.23(1) | `ClosureDescription2019.lean` | GREEN upstream |
| Lemma 2.23(2) | `ClosureFreeAmalgamCompletion.lean` | GREEN upstream for U-closed sides/overlap; editorial TODO removes undefined strong-completion clause |
| Definition 2.24 | `ClosureSemiClosed2019.lean` | BLUE: representation with checked partial lemmas |
| Definition 2.25 | `ClosureUSize2019.lean` | BLUE/PARTIAL; possible printed ambiguity recorded in TODO |
| Lemmas 2.27–2.28 | Native closed/semi-closed partite modules | PARTIAL: published weak intrinsic test statements not fully checked |
| Lemma 2.29 | `Lemma229Counterexample.lean` | **REFUTED LITERALLY (GREEN negative proof)**: explicit A,B,C0 satisfy hypotheses but no C has all intrinsically U-irreducibles covered; closed-test repair pending |
| Lemma 2.31 / Definition 2.17(4c) | `LiteralWeakRankBridge.lean` | GREEN conditional: closed rank control by fully protected original-style maps yields ALL exact weak n-vertex completions; supplying those maps remains open |
| Lemmas 2.30–2.31 | Closure rank/relative boundary modules | OPEN for the general corrected higher-rank iteration |
| Explicit non-Ramsey counterexample | `PairedEquivalences.lean`, `MatchingClosure.lean`, `MatchingHereditary.lean`, `FinitePairedClass.lean`, `MatchingFreeAmalgam.lean` | GREEN finite K, closure, closed hereditariness, literal local n=1, persistent colouring and matching core of free amalgams; general strong amalgamation and ambient ordered Ramsey class remain OPEN |

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

The current `main` audit lists 39 declarations, all with permitted logical axioms. The general class-theorem contradiction and corrected theorem are BOTH still unproved end to end in Lean. PR #11 gives a precise corrected class contract and conditional Ramsey extraction; it does not assert that its missing sparse witness exists.
