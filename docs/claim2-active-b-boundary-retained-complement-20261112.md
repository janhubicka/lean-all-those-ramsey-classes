# Track C: active B-only boundaries stay in retained E despite fresh seam collisions

**12 November 2026. Draft Lean proof pending exact-head CI.**

This is an alternative to demanding full new-seam injectivity after
every 2019 source flip.

Let New be the actual full native functional free amalgam of one
new rooted replacement Q with a FULL retained complement E.
Assume that the weak target map of Q factors entirely through
the LEFT target witness, and Q's shared-root coordinates lie
in the target common seam. Let S be the complete preimage
of that seam under the NEW weak source map. Choose any actual
B-exclusive SOURCE vertex x outside S.

The merged native monochromaticity lemma says the entire
New\\S component C of x remains B-exclusive. Since the whole
Q image lies in the target LEFT side, no source vertex of C
lies on Q's side. Full source free-amalgam coverage therefore
puts C inside the retained E image. Because Q/E shared-root
vertices map into S, C is PRIVATE to E (disjoint from the
inner gluing root).

The verified `fullFreeAmalgam_private_generatedBoundary_eq_image`
now says its **entire function-generated external boundary** is
literally the full E-image of the corresponding unchanged
generated E-boundary, including all arbitrary functional
outputs, not just graph neighbours. Thus **no Q-only source
vertex can belong to the active B-boundary**.

If the OLD weak source map was injective on the old complete
target common-seam preimage and the new map agrees on E,
the verified retained-complement injection lemma transports
that injectivity to THIS NEW B-boundary. This conclusion
holds **even if the new weak map has collisions somewhere
else on the new common-seam preimage**.

Proposed theorems:
- `fullNativeFlip_rightComponent_generatedBoundary_in_retainedComplement`
- `fullNativeFlip_rightComponent_generatedBoundary_inj_of_oldSeamInj`

### What this does and does not resolve

This is a concrete one-flip source-geometric improvement to the
Track C local trichotomy: the active remaining B-boundary may
be injective without the WHOLE new S being injective. It suggests
a weaker iterated-state invariant tracking the retained
B-active complement or its local boundaries.

The present proof does NOT automatically propagate old full-S
injectivity to later iterations, construct flippable B-only
inner geometric pieces in the smaller-root mixed branch, or
prove the terminal A-clearing contradiction. A further
relative/nested carrier proof is needed to iterate this
localized injection property through multiple selected Q flips.

Original numbered 2019 paper remains frozen; no removed TODO
is reintroduced. Protect active root, inspect exact-head full
Lean compilation, named axioms and no-admissions checks.


## 12 November refinement: retained-complement injection is the sufficient invariant

The stronger draft endpoint
`fullNativeFlip_rightComponent_generatedBoundary_inj_of_retainedSeamInj`
no longer assumes that the OLD weak map injects its entire old
target-seam preimage. It needs only that distinct source vertices
of the **retained full complement E** whose old target images lie
in the seam have distinct images. The proof identifies every
active NEW B-boundary vertex with an E source representative,
uses complete old/new target-coordinate agreement on E,
and cancels via this retained-E injectivity.

The original
`fullNativeFlip_rightComponent_generatedBoundary_inj_of_oldSeamInj`
is now a backwards-compatible corollary: global old S injection
restricts to E injection because the old E embedding is full
and injective.

This is a genuine weakening of the induction input and
suggests tracking **injectivity on the B-active nested retained
carrier**, rather than the entire seam. It still does not establish
that the next retained carrier inherits the same property
automatically: that requires a nested-complement persistence
proof along the actual same-selected-Q source sequence.
