# Track C: preserve the weaker closed-context no-escape invariant through a literal functional flip

This work is stacked on PR #869's no-escape localization predicate. Consider actual native functional full free amalgams
```
Old = OldInner +_U E
New = NewInner +_U E
```
with the **same complete native complement E**. Let SR⊆E be the retained old contextual part. Define `KOld = iOldL(OldInner) ∪ iOldR(SR)` and `KNew = iNewL(NewInner) ∪ iNewR(SR)`. Let SOld,SNew be arbitrary source seam sets (in the original 2019 proof: full weak target-root preimages).

The new theorem `fullFreeAmalgam_noEscape_preserved_under_innerReplacement` proves:

```
NoEscape(Old, SOld, KOld) =>
NoEscape(New, SNew, KNew)
```

provided (a) all inserted shared root vertices lie in SNew, and (b) the seam predicates agree coordinatewise on ALL E vertices. The new outer root does not have to be a minimal separator, and SR is not required to contain the gluing root.

**Native proof:** new left-private vertices have no full Gaifman edge outside their inserted side; new right-private edges reflect exactly into the common E and then into Old. The old no-escape condition forces any old target neighbour into its context. If it belongs to OldInner, true full-amalgam overlap identifies it with a root vertex, which belongs to NewInner; otherwise the retained right witness lies in SR. This uses complete function input/output graph tuples, not a weak incidence homomorphism shortcut.

The merged same-witness contextual flip (#844) already exports the exact EHN map equality on E, and the old/source and new/source root images are in the target shared seam. These give the two remaining seam inputs of the generic transfer when instantiated for the original Claim 2 replacement. The old context equals the actual original geometric P by the earlier exact-carrier lemma and therefore has no-escape by PR #869.

**Open after this:** specialize the generic theorem to #844's exact same forbidden-source witness, and formulate an iteration state carrying closed/no-escape contexts, full rooted all-test profiles, root coordinates, exterior A-support and interior B-rank. The original global canonical relation is indexed by genuine selected forbidden pieces; the terminal A→B flip still needs a legitimate selected geometric piece (or a new equivalent selected witness), not merely a closed no-escape context.

No intermediate left-minimality, invented weak-image quotient or frozen manuscript changes. CI/axiom check pending.
