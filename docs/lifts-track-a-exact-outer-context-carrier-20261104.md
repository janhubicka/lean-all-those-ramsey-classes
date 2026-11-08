# Section 3 Claim 2, Track A: exact older context carrier in a native nested flip

> **8 November status update:** The construction and its selected-Q
> specialization were subsequently merged and passed exact-head Lean CI.
> In particular the outer carrier and original ordered-root symbol
> preservation are proved in #899 and strengthened by #927. This
> document preserves the historical 4 November *draft* audit, not the
> current status. See [Track A closeout](lifts-track-a-closure-20261108.md).


**4 November 2026.** Validation document; the numbered original manuscript remains frozen.

**Status:** This note records an actual Lean proof attempt, NOT a verified theorem
until each exact-head CI run succeeds. PRs [#888](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/888),
[#889](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/889),
[#892](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/892)
are stacked draft branches. The selected-Q full-private-connectivity proof is
independent [#881](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/881).
Older exterior boundary/geometric reconstruction is separately
[#866](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/866),
[#876](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/876),
[#879](https://github.com/janhubicka/lean-all-those-ramsey-classes/pull/879).

## Exact mathematical setup

Let \(A\) be the original *native functional* forbidden source,
with a genuine inner selected geometric piece with complete closed
root \(U\) and selected component \(D\). Let a second, older genuine
geometric piece have closed root \(R\) and selected component \(C\).
The relevant assumption is **component nesting**
\(D\subseteq C\), *not* either \(U\subseteq R\) or \(R\subseteq U\).

Split the original source by its actual full source diagram

\[
 A=P+_U E,\qquad P=U\cup D,\qquad E=A\setminus D.
\]

The root \(R\) is disjoint from \(D\), hence is contained in \(E\).
Set \(T=i_{E,\mathrm{old}}^{-1}(R)\subseteq E\); this is an actual
function-closed subset of the unchanged full complement.
Let \(Q\) be the exact canonically selected replacement rooted over
the same entire native functional \(U\). Consider the *literal*
new full native forbidden source

\[
 A'=Q+_U E.
\]

The transported closed outer context is

\[
 K'=i_Q(Q)\cup i_{E,\mathrm{new}}
        \bigl(E\cap(R\cup C)\bigr).
\]

For an actual \(Q\)-private vertex \(q\), let
\(C'=\operatorname{Comp}(A'\setminus i_{E,\mathrm{new}}(T),i_Q(q))\).

The desired *equality of source subsets*, not merely profile equality,
is

\[
 \boxed{K'=i_{E,\mathrm{new}}(T)\cup C'.}
\]

The type-correct Lean formulation uses full \`Structure.Embedding\`
rather than the potentially noninjective weak forbidden target map.

## Three-layer proof

1. **#888 — pure free-source carrier identity.**
   Assume all retained complement vertices outside \(T\) satisfy
   old/new \(C\)-membership equivalence; every surviving common-root
   coordinate \(U\setminus T\) is in \(C'\); and every fresh \(Q\)-private
   vertex belongs to \(C'\).
   The full free-amalgam cover and exact overlap give both inclusions.
   On the forward side, every new inner vertex is either the
   full-root image (hence in \(T\) or \(C'\)) or private (in \(C'\)).
   Each retained right-side vertex is either in \(T\) or transports
   by component equivalence. Conversely, every \(C'\)-vertex is
   either from the new inner piece or the unchanged complement,
   and the retained complement's old membership follows from
   the reverse component equivalence. There is no graph-only
   short cut or hidden root-tuple injectivity hypothesis.

2. **#889 — derive the retained and root hypotheses.**
   A genuine selected replacement component with complete generated
   boundary \(U\) gives the **actual** \(A'\setminus T\) component
   containing it by merged #822, including attachment of all of
   \(U\setminus T\) and generated-neighbourhood contribution from
   \(U\cap T\). Merged #793 then gives exact *all-retained* old/new
   membership equivalence (private and common-root retained vertices
   alike). To lift **all** new inner-private vertices into this
   component, use a *separate whole-private-side connectivity*
   hypothesis; a complete generated boundary for one component
   does not imply it.

3. **#892 — derive the actual old source inputs.**
   From genuine nested \`GeometricFunctionalPieceData\`,
   the complete older root \(R\) survives in the full complement;
   \`T\` is the exact closed preimage and \(i_{E,\mathrm{old}}(T)=R\).
   The original selected inner vertex is in \(C\), and changing
   basepoints inside \(C\) gives the same actual component.
   Merged old source full-diagram geometry supplies the selected
   inner private component and covers all old inner-private
   vertices. The original generated boundary equation
   \(U=\operatorname{Cl}(N(D))\) forces \(U\setminus R\subseteq C\),
   even when \(U\) and \(R\) are incomparable. Thus #889 applies.
   Finally the original geometric outer piece's vertices are
   **exactly** \(R\cup C\), so its retained complementary preimage
   is precisely the generic retained set used in #889.

## Distinct canonical-Q witnesses: an adversarial check

Merged #805 constructs a Q-private vertex \(d\) whose component has
\(\operatorname{Cl}_Q N(C_Q(d))=U\).
Independent draft #881 constructs possibly a *different*
private vertex \(x\) for which every Q-private vertex belongs to
\(C_Q(x)\). These witnesses must **not** be silently identified.

The lemma \`functionalAllPrivate_component_reroot\`, added to #892,
shows that if all private vertices lie in \(C_Q(x)\), they lie in
\(C_Q(d)\) for *any* other private vertex \(d\), using the symmetry
of actual root-avoiding paths. The full-root boundary witness from
#805 can therefore be used with the whole-Q-private connectivity
from #881 once both branches are validated and integrated.

## Remaining integration — no theorem promotion

- **Q selected connectivity:** merge a CI-verified #881, then
  combine it with merged #805 using re-rooting, giving one
  \`dQ\` satisfying BOTH boundary and all-private membership.
- **Outer geometric piece with correct orientation:**
  the draft #876 reconstructs an older minimal-separator piece
  with preserved exterior as \`left\` and inserted Q as \`right\`.
  **Swap the distinguished components** using the already proved
  \`minimalClosedSeparator_swap\`; the outer selected piece for
  the original canonical global symbol must be rooted towards
  **inserted Q**, not towards the preserved exterior.
  Its complete old root must be enumerated by the *original*
  ordered \`Fin m\` tuple, not a newly chosen enumeration.
- **Exact contextual rooted structure:** after the above orientation
  and carrier equality, use the already merged
  \`geometricOriginalPiece_profile_equiv_transportContext\` (#862
  specialization) and conditional actual-global-symbol theorems
  #795/#796. Compare *all* forbidden native functional
  free-amalgam tests on the entire ordered root; equality of vertex
  sets alone is not enough.
- **Source support and target collision are separate:**
  Track C's positive local B-source support successor and termination,
  the final A-minimizer contradiction, and Track D's weak target root
  collision obstruction are not resolved by this source-carrier proof.

**Validation policy:** check the precise Lean declaration signatures,
full CI and named \`#print axioms\` for each exact commit, and
confirm no \`sorry\`, extra axiom, or stronger-than-paper assumption.
Keep the review-only TODO ledger; do not rewrite the numbered
2019 manuscript while proofs are still under audit.
