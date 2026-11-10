# Track A — genuine nested source flip and old GLOBAL canonical symbol

> **10 November verified-status update:** The source-side result #899,
> its complete carrier strengthening #927, and the same-selected-Q
> concrete strict-source-rank step #929 have passed exact-head Lean CI
> and are merged. Deduplication PRs #964 and #968 and the direct
> target-relation shortening #972 have also passed full CI and merged.
> The **6 November draft ledger below is historical** and should not
> be read as the present validation status. Track C's universal
> successor/terminal proof and Track D's weak-target root collisions
> remain open. See the [Track A closeout](lifts-track-a-closure-20261108.md).


**6 November 2026 | DRAFT audit ledger | frozen numbered manuscript untouched**

This note documents the exact mathematical target of
\`AllThoseRamseyClasses.Lifts.nestedGeometric_selectedFlip_preserves_outerGlobalPieceSymbol\`
in [#899](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/899).
**This is NOT a kernel-validated result until exact-head CI and
\`#print axioms\` pass.** The PR is a composite integration/test
branch; its parent drafts must be merged and the composite sources
deduplicated before promoting a stable public API.

## Proved, merged source premises

- #805, #811: a genuinely selected canonical Q has one internal
  full-root-generating component, and its literal replacement source
  has a genuine new *inner* minimal separator.
- #866: a genuinely nested original *older opposite exterior*
  survives in the unchanged complement and has complete internal
  generated boundary, rather than having this condition postulated.
- #881: all genuinely selected Q-private vertices are connected outside
  the full shared root, and a SINGLE Q-private witness has this
  connectivity together with the complete generated-root boundary.
- #888/#889: a generic source carrier theorem and its actual
  inserted-component/retained-complement specialization, preserving
  *all* complement coordinates (private and common-root).
- #862: the actual original older geometric piece has the same
  full native forbidden gluing-test profile as the transported closed
  context, provided the inner full source replacement is diagram
  equivalent.
- #795/#796: once a NEW actual geometric piece has the original
  ordered full root and its entire carrier is exactly the transported
  context, equality descends to the actual GLOBAL canonical
  piece-symbol quotient. These results are conditional but proved.

## Draft bridge under exact-head CI

- [#876](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/876):
  from one genuine original component-nesting premise and Q's
  full-root boundary, build the ACTUAL older minimal closed separator
  after the literal full native Q flip. The first failed CI was an
  improperly typed path reversal; this has been repaired using the
  already verified \`reachOutside_symm\`.
- [#879](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/879):
  use genuinely selected Q and actual finite original source to
  remove the extra new-source-finiteness and Q-boundary premises.
- [#892](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/892):
  identify the ACTUAL nested transported outer context as exactly
  the complete transported old root plus ONE chosen new T-component.
  The first failed CI identified two reversed concatenations of
  root-avoiding paths and one redundant tactic; all were patched.
- [#895](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/895):
  remove extra Q-side component hypotheses through the genuine
  selected-Q common witness.
- [#897](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/897):
  re-enumerate a REAL geometric piece by the original Fin m root
  tuple and swap the selected component from the preserved exterior
  to the newly inserted Q side. Its initial type elaboration
  failed; the subtype-vertex unfolding fix is awaiting new CI.
- [#899](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/899):
  combine the two chains with root ordering and proven global-symbol
  congruence, using the SAME genuinely selected Q and the SAME
  Q-private vertex for the complete root boundary and carrier identity.

## Required theorem contract (audit against published statement)

Original source: finite native functional \(A\in F\), actual
inner \(U\)-piece and older \(R\)-piece with
\(\mathrm{Comp}(A\setminus U,d)\subseteq
  \mathrm{Comp}(A\setminus R,p)\).
No hypothesis \(U\subseteq R\) or \(R\subseteq U\).

The replacement \(Q\) must be an actual geometrically selected
finite forbidden piece (not merely equivalent in the profile
setoid), plus its *complete original-root native gluing-diagram*
equivalence to the original inner piece. A full source diagram
\(A'=Q+_U E\in F\) is required, as provided by the separately
validated canonical flip. It is not inferred from a weak map.

The conclusion constructs an actual NEW older geometric piece
selected towards the inserted Q side, with the *exact same ordered
Fin m root coordinates through the retained full complement*,
and derives equality of the OLD and NEW originally indexed global
piece symbols. NEW finiteness is derived from genuine selected-Q
membership; it is not an extra input.

### Two distinct technical obligations

1. **Cut equality vs. root-order equality**: #876's minimal
   separator may have arbitrary finite enumeration and the
   *opposite* orientation. Mere equal sets of root vertices are
   not enough to claim the published global symbol has survived.
   #897 supplies a new actual geometric piece on exactly the old
   ordered root and with the selected side swapped.
2. **Carrier equality vs. rooted-profile equality**: complete
   generated boundaries alone do NOT imply that the whole
   transported context equals a *single* new component plus the
   root. #892/#895 prove the exact source-set identity, while
   #862/#795 independently transfer all native functional
   gluing tests and the original global quotient only after this
   identity and the full ordered root have been supplied.

The target weak EHN homomorphism-embedding may identify distinct
source vertices. None of the above uses it as an injection or
takes a forbidden target-image quotient.

## Still open beyond Track A

- Prove a genuine positive local B-only SOURCE-support successor
  under the printed Claim 2 minimization regime, preserve the
  original A-source support, and establish finite termination
  with a valid final A-to-B contradiction (Track C). A decrease
  of B-source support alone is NOT a contradiction to minimum
  A-source support.
- Resolve colliding root images in the weak target-map setting;
  original canonical symbols enforce distinct coordinates and
  cannot silently be applied to noninjective tuples (Track D).
- Discharge global shadow-avoidance / strong AP for the full
  original maximal-lift age, separate from the conditional
  source-geometric symbol preservation.

**Editorial contract:** keep numbered \`ramsey.tex\` frozen,
continue review-only TODO markers and this audit, avoid re-adding
notes that the collaborator explicitly removed. Do not mark Claim 2,
the unrestricted Section 3 lift or strong amalgamation validated
until the exact English statements and matching Lean exports
are checked.
