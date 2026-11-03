# Track F — exact Fraïssé limit / original lift theorem boundary

**2 November 2026.** This record distinguishes the already merged finite-age theorems, CI-pending interfaces, and the genuinely missing infinite Fraïssé construction for Section 3 of *All Those Ramsey Classes* (2019). The numbered `ramsey.tex` is frozen. This file is an audit / work plan, not a replacement proof.

## What the ORIGINAL maximal-lift library already proves

- [#742](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/742), CI 41254444596: `GlobalFiniteMaximalTraceAmalgamationCore` packages hereditary membership, full JEP and exact-overlap strong AP, **conditional** on `GlobalCanonicalShadowFreeAmalgamation` and native JEP. Its specialization from `GlobalMinimalWitnessGeometricConditions` retains extra hypotheses; the irreducible forbidden-source special case is genuine.
- [#778](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/778), full green CI, merged: `globalOriginalMaximalTraceAge_nonempty` constructs a REAL empty-carrier age member under regularity and nonempty connected forbidden sources. No universal finite shadow or new theorem about Claim 2 is assumed.
- [#787](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/787), full green CI, merged: `globalMaximalTraceAge_finite_onFiniteCarrier` proves the actual global regular maximal-trace age is finite on each fixed finite carrier when the ORIGINAL relation and function symbol types are finite. This includes complete partial/set-valued function fibres and any nullary old symbols.
- Already merged: `IsGlobalFiniteMaximalTrace.of_embedding`, `globalFiniteMaximalTraceAge_exact_reduct`, `globalMaximalTraceAge_finiteIsoRepresentatives`, and unconditional positive-arity JEP for connected nonempty forbidden sources.

None of these statements proves unrestricted shadow-free amalgamation for all regular HE-image-closed connected families.

## New Track F proof branches — do not mark green until full CI passes

| PR | Exact purpose | Dependency |
| --- | --- | --- |
| [#775](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/775) | Actual full functional two-singleton nullary-JEP obstruction; fixes a target empty-tuple elaboration error from earlier CI | None |
| [#807](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/807) | Lift the native nullary JEP obstruction to the **actual maximal-trace age** for empty regular F | Stacked on #775 |
| [#798](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/798) | Fully relabel any finite original maximal trace onto Fin n and construct a countable representative type covering all full isomorphism types | Merged #787 |
| [#802](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/802) | Exact finite Fraïssé **input record**: nonempty, HP/JEP/strong AP, countable full-isomorphism cover; explicit shadow avoidance, or unconditional irreducible-source instance | Stacked on #798; merged #742/#778 |
| [#804](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/804) | The ACTUAL original regular global piece-lift language is countable even when forbidden families have infinitely many pieces of unbounded widths, provided the old signature is countable | Independent |

Their states must be read from the current GitHub runs, not inferred from this note.

## What Mathlib actually exports

The checked `Mathlib/ModelTheory/Fraisse.lean` API defines
`FirstOrder.Language.IsFraisse`, `FirstOrder.Language.IsFraisseLimit`,
`FirstOrder.Language.exists_cg_is_age_of`, and
`FirstOrder.Language.exists_countable_is_age_of_iff`.
These provide the *age of a countable model* under suitable HP/JEP/countability
conditions and develop limit **uniqueness**. The file explicitly says
`TODO: Show existence of Fraïssé limits`. Thus neither the existing Mathlib
API nor a standalone `IsFraisse` proposition automatically constructs an
ultrahomogeneous limit from AP. Do not cite a nonexistent existence theorem.

There is a second semantic bridge: Mathlib first-order structures use
`FirstOrder.Language` with ordinary (single-valued, total) function symbols,
whereas our native Section 3 `StructuralRamsey.Structure` has COMPLETE
set-valued partial-function fibres and **FULL** embeddings. A faithful bridge
should relationalize each complete function graph as an old native relation
of arity one higher, then prove that the FIRST-ORDER induced substructures
used in the Fraïssé construction correspond exactly to FULL native
function-closed substructures. Merely preserving positive source-defined
function incidences is insufficient.

## Exact next theorem targets

1. **One common-carrier fully faithful encoding.** Provide a relational
   first-order signature for the complete graph of every native
   relation/function symbol and added root-injective piece predicate.
   Construct the inverse decode and prove that every relation, every
   function *value fibre*, and all full embeddings agree in both
   directions; include old nullaries, repetitions and undefined inputs.
2. **Essential countability and nonempty age.** Use the actual `Fin n`
   representative cover (#798), the countable lifted signature (#804),
   and #778 to instantiate the predicates required by the first-order
   age interface. Do not replace `Countable` of *isomorphism types* with
   countability of all structures on every arbitrary carrier.
3. **Construct the limit, rather than assuming it.** Enumerate all finite
   age objects and extension diagrams, build a nested chain of
   finite age members by JEP and (strong) AP, and take a countable
   direct limit. At each step show the limit's native function graphs
   agree on every old finite root with their complete original fibres.
4. **Extension/homogeneity.** Prove every finite full embedding into
   the limit can be extended along any finite age embedding; derive
   ultrahomogeneity by the back-and-forth construction. This is
   the missing *existence* content not currently exported by Mathlib's
   Fraïssé file.
5. **Extra model-theoretic conclusions.** The original Section 3
   existential completeness, universality for the correct `Forb_{EHN}`
   class, and omega-categoricity in the finite **relational** signature
   need distinct proofs. None is entailed solely by an arbitrary
   countable homogeneous expanded structure in an infinite signature.
6. **Ramsey theorem remains separate.** The published `thm:main`
   additionally requires the original regular-family strong AP /
   shadow-avoidance lemma (Tracks A–D), an actual Ramsey-local
   completion theorem, all expanded-type copy transfers, and the
   appropriate admissible/ordered language and weak-substructure
   hypotheses (Track E). A typewise arrow does not give full Ramsey.

## Adversarial failure checks

- Nullary FULL JEP is not automatic even for the empty forbidden family:
  opposite truth values of an old nullary relation have no common full
  target. The manuscript's review-only TODO is **ATRC-073** (PR #191
  merged). **ATRC-072 belongs to Track E** and must not be reused.
- A certificate `#print axioms T` checks `T` **including its hypotheses**,
  not the removal of those hypotheses. Never mark `mainthm` green
  while `GlobalCanonicalShadowFreeAmalgamation` remains an external
  premise for reducible sources.
- "The shadow of the strong amalgam is free" is a separate exact
  source-level statement from mere exact-overlap strong AP.
- Do not identify the **alternative folded finite-family lift**
  (which allows repeated root coordinates) with the original
  root-INJECTIVE global canonical piece lift.
- Keep `ramsey.tex` frozen. Record corrections only in validation
  TODO notes and separate audited formalization documents.
