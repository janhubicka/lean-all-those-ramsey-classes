# Track C — the correct final A-support contradiction

The 2019 Section 3 Claim 2 selects a weak forbidden EHN witness minimizing ORIGINAL left-exclusive **source** support. Intermediate B-to-A flips need not preserve this minimality: they may increase left-exclusive support inside the outer piece.

Instead keep the **exterior** A-only source count fixed. Let (O) be the original geometric outer piece, and let (O_{final}) be the final transported outer context after all inner B-only flips and a final outer A-to-B replacement.

The only arithmetic conditions needed are:

- The original map has at least one A-only source vertex in (O).
- The final map has NO A-only source vertex in (O_{final}).
- The number of A-only source vertices **outside** the two outer contexts is equal.

Then

```
A_total(initial) = A_inside(initial) + A_outside(initial)
                 > A_outside(initial)
                 = A_outside(final)
                 = A_total(final)
```

The exact-counting proof does not assume monotonicity of total A-support during intermediate B flips.

## Lean declarations

- `finiteSourceSupport_terminalLeftDrop_of_outsideEq`: finite source cardinality arithmetic, original positive inside support + final zero inside support + exact outside support equality implies strict total support drop.
- `geometricInnerSubpiece_outsideSupport_card_eq`: for one genuine nested functional replacement, prove identical outside-context SOURCE support for ANY target subset using the actual full complement embedding and map agreement. This is the concrete per-step A-exterior invariant.
- `claim2_outsideLeftCount_eq_of_reachable`: equality of any numeric outside-source invariant along a finite path, even when the state packages varying source carriers.
- `claim2_exists_terminal_with_constant_outsideLeft`: well-founded local B-descent yields a terminal state whose exterior A-support equals the original.
- `minimalForbiddenEHNWitness_no_terminalLeftClearingFlip`: constructs the final forbidden source witness and contradicts the ORIGINAL support-minimizer.

## Still OPEN

1. Need the concrete Claim 2 contextual successor relation to preserve a genuine geometric outer piece; the current merged one-step theorem only provides a closed transported context and the separate exact outer profile theorem (#777).
2. Need a uniform mechanism for choosing the next B-only proper subpiece until terminality; the well-founded theorem does not assert a next flip exists.
3. Need to show that terminality entails a full outer A-to-B native source flip eliminating every A-only source vertex inside the final transported context.
4. The concrete per-step equality of exterior A-support is now formalized for an actual inner replacement; instantiate it for *each* successor along the iteration using the exact associated context and same native target map.
5. Source-root noninjectivity remains the distinct Track D obligation.

**Do not mark unrestricted Claim 2 or the original global strong amalgamation/Ramsey statement validated.** This change is independent of edits to the frozen mathematical manuscript and contains no axiom/sorry shortcut. Exact-head CI and named `#print axioms` remain required.
