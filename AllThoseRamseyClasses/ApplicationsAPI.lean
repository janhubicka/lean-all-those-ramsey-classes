import AllThoseRamseyClasses.PublicAPI
import AllThoseRamseyClasses.Applications.PaperAcyclicDigraphs
import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import AllThoseRamseyClasses.Applications.PaperForbiddenIrreducibles
import AllThoseRamseyClasses.Applications.PaperPointedEquivalences
import AllThoseRamseyClasses.Applications.PaperTotalUnaryFunctions
import AllThoseRamseyClasses.Applications.PosetRamseyTheorem
import AllThoseRamseyClasses.Applications.SteinerLocalCompletion

/-!
# Verified application theorems

Import this module (or `AllThoseRamseyClasses`) for the corrected 2019
multiamalgamation theorem and *completed* class-level applications.

Completed applications now include finite ordered posets, freely ordered
digraphs and simple graphs, ordered acyclic digraphs, K_n-free graphs,
pointed equivalences, and the finite-target m-unary-function case.
The freely ordered partial Steiner triple class is a separately completed
**auxiliary** example not included among the paper's examples.
The named poset representation has one inert empty binary relation;
its vertex order `.lt` is strict, whereas the paper uses a reflexive order.

The additional acyclic-digraph-with-linear-extension corollary from
the paper is proved using the B-copywise forward-edge deletion lemma.

The freely ordered digraph and simple-graph results from the paper are
proved separately using ordered relational Ramsey and the genuine free
amalgamation criterion; their order is the distinguished external order.

The freely ordered pointed-equivalence Ramsey class from the paper is
proved via its full idempotent unary-function encoding.

The finite-target part of the paper's m-unary-function Ramsey theorem
is proved separately; the infinite-target clause remains open.

The freestanding partial-function theorem 2.19 is exported by
`PublicAPI`. Other `Applications/*` modules document further Lean-proved components,
whose still-open class-level Ramsey conclusions are not exported here.
-/
