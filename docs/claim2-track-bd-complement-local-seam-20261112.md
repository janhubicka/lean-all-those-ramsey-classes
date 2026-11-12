# Track B/D: exact complement-local seam injectivity

**12 November 2026 — proposed source-side strengthening.**

The already kernel-verified native seam-collision localization #1043
requires the old weak EHN map `f` injective on the ENTIRE seam
preimage `f ⁻¹' Seam`. Inspection of its proof shows that the only
old source vertices compared are in the image of the unchanged
FULL native complement embedding `iOldE`.

## Sharper direct theorem

`fullNativeReplacement_retainedComplement_seamInjective_of_local`
uses only the weaker hypothesis:

```lean
Set.InjOn f (Set.range iOldE ∩ (f ⁻¹' Seam))
```

It proves no two retained-complement vertices whose target images
belong to Seam can collide after an exact complement-preserving
source replacement.

`fullNativeReplacement_newSeamCollision_hits_QOutsideComplement_of_local`
identifies an actual new Q-only SOURCE vertex outside the retained
complement whenever a NEW target seam collision occurs. This
uses FULL native free-amalgam coverage, not a quotient of target
images. It does not claim the new map is seam-injective.

Finally,
`fullNativeReplacement_newSeamInj_of_local_and_QrootReflection`
adds a precise sufficient condition: if every Q vertex mapped
into the target Seam is already in Q's full embedded root,
the NEW complete seam preimage is contained in the old
complement, and the NEW map is injective on it.

This is a strict logical strengthening of the old source hypothesis
and isolates Q-root reflection as an explicit, still unproved
condition for the actual selected-Q flip. The result is
independent of finite carrier sizes, source support minimizers,
forbidden-family image closure and any strong AP conclusion.

## Important limitations

The actual canonical selected-Q flip is NOT known to satisfy
Q-root reflection, and the old complement-local seam injection
is not automatic from injectivity merely on the outer ordered root.
No source image is quotient-identified. The printed 2019 TeX and
all collaborator-removed TODO notes remain untouched.

## Verification

Do not mark the new proof validated until an exact-head
full project Lean build, three named `#print axioms`,
permitted-axiom inventory, source/contract audits, protected
active-root check, and no-admissions scan all succeed.
