# Track C — finite descent of a noncapturing genuinely mixed smaller piece

14 November 2026. Stacked on draft #1164. Exact-head Lean CI pending.

New independent finite source-set fact:
`finiteSourceSubtype_card_lt_of_proper` states that genuine
proper set inclusion S ⊂ T in one finite SOURCE carrier V yields
`Nat.card {v : V // v ∈ S} < Nat.card {v : V // v ∈ T}`.
The proof uses an actual native source-set subtype embedding and
finite injective-nonsurjective pigeonhole; NOT a target-image rank.

`claim2_smallerRoot_noCapture_finiteProperDescent` combines that
cardinality with #1164's exact genuine source nesting and inheritance
of the LOCAL complete generated B-active boundary-injectivity predicate.

The theorem remains valid when the selected smaller component
contains A-exclusive source vertices: A-freeness does not enter
the source nesting or local injection restriction. This makes the
A-mixed/no-capture branch a candidate for strict well-founded
descent on actual geometric piece SOURCE size, rather than
assuming an immediate flippable B-only inner component.

IMPORTANT LIMITATIONS:
* It does NOT prove that a given smaller-root alternative avoids
  capturing an old outer root.
* It does NOT derive an A-anchor and positive B-source rank INSIDE
  d without actual A/B-exclusive source witnesses.
* It does NOT show the old global canonical symbol is unchanged
  when reselecting d as a new outer piece, or prove the original
  terminal A-clearing contradiction.
* It does NOT confuse m (the number of d-root source vertices)
  with the strictly smaller full piece SOURCE vertex count.

The frozen original 2019 source remains unchanged, and no removed
collaborator TODOs are restored. Two named axiom checks and one
protected active root.
