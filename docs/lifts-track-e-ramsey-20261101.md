# Lift formalization — Track E: finite-family Ramsey endgame

**Date:** 2026-11-01. **Scope:** the *alternative* finite named family,
all-closed-component, folded-root maximal **induced-trace** age, not the
original regular infinite-family Section 3 lift. **Main baseline:**
`380804cceffe82e43023c0a3afe3c4e3946b3eec` (PRs #737/#738 merged).
This workstream must not change the frozen numbered `ramsey.tex`.

## Previously verified ingredients (no new claims)

* `IsFiniteNamedMaximalTrace`: actual full functional old shadow;
  finite forbidden-free maximizing witness; induced ALL component tags
  along the root, with colliding tuple coordinates allowed.
* `IsFiniteNamedMaximalTrace.of_embedding`: heredity under **full expanded**
  embeddings, not under arbitrary old-shadow reductions.
* `finiteNamedMaximalTraceAge_exact_reduct`: the finite old shadows are
  **exactly** those avoiding the finite named EHN forbidden family.
* `finiteNamedMaximalTraceFibre_nonempty_iff_avoids` and
  `finiteNamedMaximalTraceFibre_finite`: genuine nonempty finite fibres.
* `finiteNamedMaximalTraceAge_strongAmalgamation`: actual finite strong
  amalgamation of the expanded class. A full native free amalgam of the
  source *witnesses* is extended to a profile-maximal witness; the final
  induced trace may introduce mixed new tag relations.
* `finiteNamedMaximalTraceAge_JEP_connected_positiveArity`: JEP
  conditional only on the indicated connectedness and positive-arity
  hypotheses. Neither AP nor JEP implies Ramsey.

## New Track E endpoints

1. `functionalArrow_of_BCopywiseCompletion` (generic functional
   language): if a finite Ramsey control has `A -> (B)^1_k`, and a
   vertex map into a target is an actual FULL `Structure.Embedding` on
   **every B-copy**, then the target has the arrow as well.
   Pull back colours on liftable A-copies, choose a default colour on
   the others, and use only liftable A-copies within the selected B-copy.
2. `finiteNamedTraceArrow_of_copywiseCompletion`: packages a genuine
   finite maximal-trace completion, including its age membership.
3. `finiteNamedOrderedTraceArrow_of_copywiseCompletion`: same result
   after adjoining a **distinguished external linear order**, as needed
   for the functional EHN Ramsey theorem.
4. `finiteNamedTraceCopywiseCompletion_of_embedding`: verifies the
   strictly stronger special case when the entire control has a full
   embedding into an age member.

All of these are **implications**, not existence proofs of their
completion premises. No axiom, `sorry`, or unrestricted Ramsey theorem
has been introduced intentionally. Keep checks in
`CheckAxiomsFunctionalCopywiseRamseyTransfer.lean` and
`CheckAxiomsFiniteFamilyMaximalTraceRamseyTransfer.lean`.

## Adversarial proof obligations still open

**E1. Ambient ordered control.** Fix two finite *ordered* trace-age
members `A*` and `B*` and a nonempty finite colour set. Apply the
all-arity functional EHN Ramsey theorem to the class of **all finite
ordered functional structures in the expanded finite-family language**.
Check the free-amalgamation-class instance used for that invocation,
including nullary functions, complete output-value fibres and any
nullary added tag predicates. The resulting control `C0` is not
assumed to belong to the trace age.

**E2. Genuine local-completion bound.** After `B*` and `C0` are
fixed, choose `n(B*, C0)` *before* constructing a sparse Ramsey
picture. Establish a theorem that bounded tests of the **original
weak induced** vertex subsets of the picture, together with the
required protected closed irreducible tests, imply existence of a
finite maximal-trace age member `D*` and one vertex map `f` which is
a **full ordered embedding** on every `B*`-copy. Do not confuse full
functional embeddings with weak EHN homomorphism-embeddings, or replace
weak subsets by closure hulls.

**E3. Compatibility of root profiles across the completion.** The
new component predicates are the ALL-CLOSED-COMPONENT folded lift
(repeated root images allowed), not the original 2019 distinct-root
canonical lift. The finite maximizing witnesses must remain maximal
along the *displayed root*. Show exact positive and negative tag
reflection on each B-copy. Witness monotonicity alone gives only
the positive direction.

**E4. Formal class-level ordered Ramsey theorem.** Use the completed
ordered arrow from E1–E3 for all finite ordered age members and colour
types. Its conclusion is a finite ordered Ramsey witness with a
**verified** finite age member, not a target defined merely by a
universal premise that restates Ramsey.

## Things that must NOT be inferred

* The age's **strong amalgamation** does not make it a functional
  free-amalgamation class: mixed tag relations can appear upon maximal
  extension. Applying `FreeAmalgamationClass.orderedRamsey_allArity`
  **directly** to this age would be unjustified.
* Finite forbidden-family signatures and nonempty finite expansion
  fibres do **not** alone give the local-completion bound.
* A full embedding of all of `C0` into some age member would suffice,
  but no such universal embedding is supplied by the current theorems.
* The separate unrestricted Claim 2, its source-geometric root
  collision and original `ramsey.tex` validation markers
  ATRC-068–071 remain owned by other tracks. Track E cannot promote
  their verification status.

**Review gate:** full all-module Lean CI; named `#print axioms` checks;
no-admissions/source-integrity scripts; review exact theorem signatures
for hidden restated Ramsey premises. CI passing these new implications
does not make E2–E4 completed.
