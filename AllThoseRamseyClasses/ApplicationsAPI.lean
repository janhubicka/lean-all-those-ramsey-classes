import AllThoseRamseyClasses.PublicAPI
import AllThoseRamseyClasses.Applications.PaperAcyclicDigraphs
import AllThoseRamseyClasses.Applications.PaperAdmissibleRamseyClass
import AllThoseRamseyClasses.Applications.PaperAdmissibleFreeAmalgamation
import AllThoseRamseyClasses.Applications.PaperLoopFirstDigraphs
import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import AllThoseRamseyClasses.Applications.PaperForbiddenIrreducibles
import AllThoseRamseyClasses.Applications.PaperPositiveForbiddenTournaments
import AllThoseRamseyClasses.Applications.PaperPositiveForbiddenAllDigraphs
import AllThoseRamseyClasses.Applications.PaperPointedEquivalences
import AllThoseRamseyClasses.Applications.PaperTotalUnaryFunctions
import AllThoseRamseyClasses.Applications.PosetRamseyTheorem
import AllThoseRamseyClasses.Applications.SteinerLocalCompletion
import AllThoseRamseyClasses.Applications.TotallyOrderedRelationsFiniteSignature

/-!
# Verified application theorems

Import this module (or `AllThoseRamseyClasses`) for the corrected 2019
multiamalgamation theorem and *completed* class-level applications.

Completed applications now include finite ordered posets, freely ordered
digraphs and simple graphs, ordered acyclic digraphs, K_n-free graphs,
and arbitrary forbidden-tournament families in finite digraphs,
pointed equivalences, the loop-first admissibly ordered digraphs,
and general relational admissible-order Ramsey class transfers, together
with the finite-target m-unary-function case.
The freely ordered partial Steiner triple class is a separately completed
**auxiliary** example not included among the paper's examples.
The named poset representation has one inert empty binary relation;
its vertex order `.lt` is strict, whereas the paper uses a reflexive order.

The additional acyclic-digraph-with-linear-extension corollary from
the paper is proved using the B-copywise forward-edge deletion lemma.

The freely ordered digraph and simple-graph results from the paper are
proved separately using ordered relational Ramsey and the genuine free
amalgamation criterion; their order is the distinguished external order.

The arbitrary-family irreducible-pattern theorem and the source-matched
positive tournament-avoidance theorem are now compiled in this API.
For induced tournament avoidance in unrestricted digraphs use
`freelyOrderedTournamentFreeDigraphs_areRamsey`; for Henson-style
positive-copy avoidance in oriented digraphs use
`freelyOrderedPositiveTournamentFreeDigraphs_areRamsey`. For the
stronger source-matched POSITIVE omission condition allowing loops
and digons in ambient digraphs use
`freelyOrderedPositiveTournamentFreeAllDigraphs_areRamsey`.
This follows from the general positive-family theorem via all full
relational extensions of each irreducible forbidden pattern.

For the literal generic RELATIONAL admissible-order statement import
`AdmissibleOrders.hasTypeAdmissibleRamsey_of_hasFreeOrderRamsey`;
it assumes only Ramsey with freely chosen orders and imposes no
free-amalgamation hypothesis. The class-level free-amalgamation
specialization is
`AdmissibleOrders.admissiblyOrderedFreeAmalgamation_areRamsey`.
The source-matched concrete digraph instance is
`PaperGraphs.loopFirstOrderedDigraphs_areRamsey`.
This does not certify the printed proposition for arbitrary
functional languages without a separate singleton-type bridge.

The finite relational language of totally ordered relations (`thm:TO`)
is proved by `TotallyOrderedIncidence.genuinelyTotallyOrderedRelations_areRamsey_finiteSignature`:
it orders genuine positive relation-instance subtypes, employs full
induced embeddings of the doubled-arity encoding and needs NO
additional symbol-order premise. The proof uses a free auxiliary
functional Ramsey class and copywise projection of the weak target.
No metric or infinite-language Ramsey statement is inferred.

The freely ordered pointed-equivalence Ramsey class from the paper is
proved via its full idempotent unary-function encoding.

The finite-target part of the paper's m-unary-function Ramsey theorem
is proved separately; the infinite-target clause remains open.

The freestanding partial-function theorem 2.19 is exported by
`PublicAPI`. Other `Applications/*` modules document further Lean-proved components,
whose still-open class-level Ramsey conclusions are not exported here.
-/
