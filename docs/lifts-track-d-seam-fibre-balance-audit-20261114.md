# Track D — seam-fibre collision minimization audit (14 November 2026)

This concerns the **original 2019** Section 3 native functional language and genuine EHN source maps. The numbered manuscript stays frozen, and collaborator-removed TODOs are not reinstated. No unrestricted Claim 1, Claim 2, strong AP or Ramsey theorem is claimed. In particular, a weak source image is not presumed to be a full induced forbidden image.

## Exact finite counting formula (English proof, not yet a Lean general theorem)

Let \(V\) be the finite set of **original source vertices**, \(T\) any target set, \(X\subseteq T\) the actual complete target common seam, and \(f:V\to T\). Count **ordered** distinct-source collisions by

\[
C_X(f)=|\{(u,v)\in V^2:u\ne v,\ f(u)=f(v)\in X\}|.
\]

Choose \(a\in V\), \(s=f(a)\in X\), and \(t\in X\setminus\{s\}\). Let \(g(a)=t\), \(g(v)=f(v)\) for \(v\ne a\). Put \(k_s=|f^{-1}(s)|\ge1\) and \(k_t=|f^{-1}(t)|\ge0\), counting **all original source vertices**, not only roots of a selected geometric piece. Then

\[
\boxed{C_X(g)-C_X(f)=2\bigl(k_t-(k_s-1)\bigr).}
\]

**Proof.** Every ordered pair avoiding \(a\) has identical collision status under \(f\) and \(g\). Previously \(2(k_s-1)\) ordered collision pairs touch \(a\), namely the pairs involving the other \(s\)-fibre vertices. Afterwards \(2k_t\) pairs touch \(a\), namely the pairs involving the original \(t\)-fibre vertices. Both target points are in \(X\). Subtracting proves the identity. A strict drop occurs **exactly when \(k_s\ge k_t+2\)**; equality occurs when \(k_s=k_t+1\). The move need not preserve EHN.

For the already verified support-first, seam-collision-second *forbidden EHN witness* minimizer (EHNLexMinimalSeamCollisionWitness.lean), an admissible single-source-vertex seam recolouring with \(k_s\ge k_t+2\) would contradict minimality. Therefore such a proposed map must **fail at least one** of the original positive-relation, native-function (input **or** output), or irreducible-FULL-test local checks of ehn_oneVertexRecolor_failure_has_localNativeWitness. This is a conditional consequence of the counting calculation and already formalized native minimization/locality results. It does NOT construct a successful EHN recolouring.

## Finite Lean counterexample to a root-only descent argument

Take \(V=\{0,1,2\}\), \(X=T=\{0,1\}\), and \(f=(0,0,1)\). The selected distinct root coordinates \(\{0,1\}\) both map to \(0\); hence the root has width \(2=|X|\) and seam point \(1\) is *unused by those root coordinates*. Yet the **whole** source map already uses seam point \(1\) via original source vertex \(2\). Recolour source vertex \(0\) to \(1\), giving \(g=(1,0,1)\). Then the selected root images are injective, but

\[
C_X(f)=2=C_X(g),\qquad k_0=2,\quad k_1=1.
\]

Thus no strict secondary descent follows from root injectivity and root-level target vacancy. **In fact the three-to-two example is globally collision-minimal among EVERY map from the three original vertices to the two-point seam, even allowing simultaneous recolouring of all vertices:** by the pigeonhole principle some two vertices collide and contribute at least two ordered pairs. The new Lean theorem seamFibre_anyFullSeamMap_hasAtLeastTwoOrderedCollisions checks this exact universal finite lower bound. The balanced old fibre sizes (2,1) attain that lower bound. EHNSeamFibreBalanceCounterexample.lean is a small *decidable Lean regression* certifying these **bare coordinate/cardinality facts**, not a new EHN or forbidden-family example. The conclusion is independent of canonical-lift compatibility.

## Adversarial proof-control gates

1. Count the full original source fibres over the **whole** target seam. A spare point relative to a selected root need not be spare relative to the forbidden-source witness. Even a root-injectivizing change can have unchanged global collision count.
2. For an occupied destination seam point \(t\), the precise one-vertex strict-drop threshold is \(k_s\ge k_t+2\). The globally unused-point lemma (#1163) is the special case \(k_t=0\), but no existence of such a point follows from a root-width bound (#1161).
3. If all seam fibres are balanced, i.e. any two have sizes differing by at most one, no one-vertex seam move decreases the ordered collision count. Therefore a one-point recolouring descent is not an unrestricted argument, even *before* EHN preservation is addressed.
4. Even when a move would improve the numerical invariant, full EHN must be rechecked: old positive relation inputs, **every** positive native function incidence involving a changed input **or output**, and FULL target embeddings for irreducible source tests meeting the change set (#1176, #1185). Common **added** canonical profiles are false/false on collapsed ordered roots (#1149).
5. A selected minimal function-closed separator can discard the input coordinates of the original unliftable incidence. A saturated separating hull is not a source-profile-compatible selected piece just because it contains some root vertex (#1137, #1145).
6. Pairwise irreducible-source-test coverage conditionally gives root-image injectivity and Claim 1 (#1190). Connectedness and minimal separator selection do **not** imply that coverage. On a colliding root the missing joint full test must be handled, not assumed away.

## Next precise Lean endpoint

Formalize the **general boxed fibre-transfer formula** for finite \(V\), arbitrary \(T,X\), then combine it with the **existing** EHN one-vertex local-trichotomy API to obtain the \(k_s\ge k_t+2\) obstruction *without* requiring a target point globally unused by the original witness. This narrows the combinatorial step but does not solve the native EHN map construction, forbidden piece profile transport, or source-support-decreasing actual Claim 2 flip.

Do not infer a general family strong-AP theorem from this note or from the finite regression. The hard original maximal-common-lift argument remains open.
