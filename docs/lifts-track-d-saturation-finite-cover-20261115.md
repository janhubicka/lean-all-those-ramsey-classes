# Finite representative cover for the repaired family

The new native module FullRangeSaturationFiniteCover replaces the former English-only bounded-table counting step with a concrete Lean candidate.

Assume finitely many old relation and function symbols, and a bound N on the size of every original forbidden member. A saturated target is the vertex-surjective image of an original finite source, so it has size at most N. Define representatives as the dependent sum over n : Fin (N+1) of actual saturated structures on Fin n.val. Existing full native table-counting proves this type finite. Existing full relabelling transports any saturated structure to one of these representatives. Cancellation of the relabelling embedding from the original EHN map proves that the representative really remains in the saturation; this does not assume the original forbidden family is already isomorphism closed.

The cover supplies a surjective FULL native embedding of a representative into each saturated member, preserving all relation truth values and complete function-value fibres. Thus this is an actual finite full-isomorphism cover, not just a finite collection of guessed source tables. The result allows functions; only the later arbitrary-image normal form requires function-free syntax.

This proves neither image closedness for arbitrary native EHN ranges nor preservation of regularity for unbounded infinite families. The conversion of this finite cover into the existing global geometric-piece regularity API and Track C iteration remains separate. All three new theorem declarations await exact-head full CI and named axiom checks. Frozen numbered TeX remains unchanged.
