# Track C — B-active source carrier is exactly retained-complement image

13 November 2026. Stacked on #1132; requires exact-head Lean CI.

The new theorem `fullNativeSelectedOuter_Bactive_carrier_eq_retained_image`
proves the **literal SOURCE-vertex set equality**

```
{w | w ∈ NewPart ∧ flip w ∈ BActive}
 =
iNewE '' {e | iOldE e ∈ OldPart ∧ f (iOldE e) ∈ BActive}.
```

Assumptions: exact native new outer carrier, new inserted Q has no
B-active target, and old/new weak maps agree on the entire retained
E complement. Uses #1132's unique E source representative and
survival theorem. No target-map injectivity and no quotient counting.

This is a precise interface for deriving equality of retained-source
B-counts and then combining it with the strict internal B-rank drop
from #1120. It **does not itself prove** strict B-count reduction,
injection of generated active boundaries, original global
minimality, mixed-smaller-root elimination or terminal exit.

The numbered original paper remains untouched; no collaborator TODOs
were reinstated. One named axiom check and protected active-root entry.
