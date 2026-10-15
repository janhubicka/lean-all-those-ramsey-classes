import AllThoseRamseyClasses.PublicAPI
import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import AllThoseRamseyClasses.Applications.PaperPointedEquivalences
import AllThoseRamseyClasses.Applications.PosetRamseyTheorem

/-!
# Verified application theorems

Import this module (or `AllThoseRamseyClasses`) for the corrected 2019
multiamalgamation theorem and *completed* class-level applications.

Currently the independently checked nontrivial class instance is the
Ramsey class of finite posets with a chosen linear extension.
The extra empty binary relation in its named Lean ambient language is
inert; `.lt` is strict, whereas the paper uses a reflexive linear order.

The freely ordered digraph and simple-graph results from the paper are
proved separately using ordered relational Ramsey and the genuine free
amalgamation criterion; their order is the distinguished external order.

The published pointed-equivalence theorem is proved in its exact total
idempotent unary-function encoding, by the checked functional EHN theorem.

The freestanding partial-function theorem 2.19 is exported by
`PublicAPI`. Other `Applications/*` modules document useful Lean-proved
components, but their class-level Ramsey conclusions are not certified
and are deliberately not aggregated here.
-/
