# Track E — finite-family folded maximal-trace Ramsey validation

**Audit date:** 1 November 2026. **Scope:** the alternative finite named
all-closed-component folded-root lift with repeated root images, not the
original regular infinite-family / distinct-root lifting theorem of
the frozen 2019 manuscript. The numbered `ramsey.tex` is unchanged.

## Certified infrastructure

The finite named maximal *induced-trace* age already has actual
full-functional heredity, exact forbidden-free native reduct,
nonempty finite expansion fibres, and strong amalgamation.
The last property is **not** free amalgamation in the expanded
tag language: maximization can add mixed component predicates.
For a family of nonempty connected sources and positive native arities
the age also has JEP. None of these facts alone proves Ramsey.

* **PR #743, merged `2b1cc8bf`, green full Lean CI:** an unconditional
  all-arity finite **ordered ambient** Ramsey control in the entire
  extended functional language, and generic full-functional
  B-copywise Ramsey-arrow transfer. The control is not required to
  belong to the maximal-trace age.
* **PR #757, merged `cf7e43e7`, green full Lean CI:** from a single
  finite forbidden-free **native common witness** D and compatible
  full embeddings of each chosen B-maximizing witness into D, one
  finite maximal extension yields an actual maximal induced-trace
  completion. All original set-valued function fibres and BOTH
  truth values of the folded tag predicates are reflected on the
  protected copies; the ordered version requires compatible order
  on each protected copy.
* **PR #764, merged `c7d39ea0`, green full Lean CI:** the strictly
  weaker **marked-copy** Ramsey transfer, matching the manuscript:
  choose a larger witness `Bbar` with a marked full B-copy.
  From an arrow `C -> (Bbar)^A_k`, it suffices to preserve the
  marked B-copy inside **each Bbar-copy**, not every B-copy of C.
  The full native-avoidance endgame constructs one genuine finite
  maximal-trace target with the ordered arrow.

The corresponding named `#print axioms` audits, all-module builds,
source-contract checks and no-admission checks passed on the listed
merged PR heads. Do not infer that the full age Ramsey theorem passed.

## Critical E2 adversarial correction: ordinary EHN is too strong

**PR #760 was closed without merge as an obsolete approach.**
Its strong local-to-global implication is true, but the assumption
that every exact weak restriction has an **ordinary EHN
homomorphism-embedding completion** is generally too strong
for native partial/set-valued functions.

Concrete obstruction: take a language with one unary partial function,
a forbidden one-point source F where that function is undefined, and
a finite native target D where the function is defined everywhere.
Then D forbids F under EHN homomorphism-embeddings (the source
singleton is irreducible, so its function fibre must be reflected).
Choose x in D whose function value y differs from x. In the literal
weak restriction S={x}, y is deleted and the function at x becomes
undefined. Hence F fully embeds in `D.weakInduce S`, even though it
cannot embed into D; by composition, no ordinary EHN completion of
that weak test into a finite forbidden-free target exists.

Thus the stronger hypothesis is not even **necessary** for native
forbidden avoidance. A proof that relies on it as a general E2
invariant would not establish the claimed finite-family theorem.

The correct predicate is already available in pinned
`PartiteConstruction.Functional.AmbientRelativeWeakFunctions`:

`IsAmbientRelativeWeakHE D S W g`

It preserves positive weak incidences, requires equality of a
nonempty function fibre only when **all its original ambient outputs**
lie in S, and protects only genuinely FULL irreducible ambient
substructures whose images lie in S. It does NOT protect spurious
irreducibles created by clipping output fibres.

**PR #769 (CI pending)** proves the precise finite-family **iff**:
for a finite native D and any n at least the maximum size of a
named forbidden source,

`AvoidsFiniteNamedEHN Family D`
`<-> FiniteNamedAmbientRelativeWeakCompletions Family D n`.

The nontrivial direction composes a putative forbidden EHN map
with the ambient-relative completion on its literal size-bounded
weak image. Conversely the literal weak inclusion `S -> D`
satisfies the ambient-relative condition for every S if D itself
is forbidden-free. The iff is independent of any source-map
injectivity, function closure of S, or extra tag reflection.

## Remaining bridge workstreams

* **Order and canonical enlarged witness:** PR #768 (CI pending)
  proposes a linear order on any finite maximizing native witness
  extending a prescribed ordered B-root injection. PR #770 (CI
  pending) lifts the native root embedding to a FULL embedding of
  the expanded B-trace into the actual folded canonical lift of
  its maximizing witness, including the order when compatible.
  This replaces an arbitrary Bbar-choice premise by the actual
  canonical witness.
* **E2 sparse-control construction — still open:** for a fixed ordered
  A*, B*, their canonical Bbar, and a finite colour type, construct
  a finite ordered Ramsey picture C with
  `C -> (Bbar)^A*_k` and finite forbidden-free
  **ambient-relative** weak completions on all literal S of size
  up to a cutoff covering the forbidden sources. This is the
  missing partite/sparsening theorem; neither the ambient Ramsey
  control nor the static locality equivalence constructs C.
* **Class-level endgame:** after E2, use #769 to infer forbidden
  avoidance of the native shadow of C, then #764 to maximize its
  native shadow and transfer the ordered Ramsey arrow into
  the actual finite maximal-trace age. This is a short consequence
  once the E2 construction is proved; keep its new hypothesis
  visible until then.

The cutoff is on the **original weak vertex set**, never its
function-closure hull. Use the corrected 2019 local-completion
quantifier order: fix B and the ambient control, choose a cutoff,
then verify every exact weak test. Preserve complete original
function fibres on actual full copies, not on artificially
truncated weak irreducibles.

## Review boundaries

- Strong AP of the lifted age is not free AP in added tags.
- A globally full embedding of an arbitrary ambient control into
  an allowed native structure cannot be assumed.
- Finiteness of the component signature and finite maximal-profile
  space does not bound the size of a maximizing witness.
- The original arbitrary regular infinite-family Claim 2,
  source-image collisions, nested functional flips and opposite
  generated boundary remain separate (ATRC-068–071).
- The review-only manuscript note is ATRC-072; do not promote the
  numbered `ramsey.tex` text or the original theorem status.

**CI gate for subsequent PRs:** full all-module Lean build, named
axiom checks, import/source integrity, conditional source contracts,
and literal no-admissions scanner. Verify exact theorem hypotheses;
a conditional statement with a proved implication is not a proof of
its consequent.
