# Claim 2: weaker source-geometric invariant for iterating a closed context

The merged same-witness inner flip (PRs #777 and #844) produces a new **function-closed** transported context K' and proves complete all-test outer profile equivalence, preserved ordered target root coordinates, strict interior B-source descent and conserved exterior A-source count. Track A still lacks a general proof that K' itself is a genuine MINIMAL closed-separator geometric piece.

The new predicate `FunctionalContextNoEscapeOutsideSeam A S K` captures exactly the **no Gaifman edge from K outside the shared-root-preimage S to outside K** condition. It does not demand that K be a single connected R-component, that the inherited root R be minimal, or that K be a selected forbidden piece.

Three native Lean lemmas (subject to exact-head CI):

1. Every genuine geometric outer piece P=R∪C with R⊆S has this no-escape property.
2. Every full S-component that starts in a no-escape K is entirely contained in K.
3. If both S and K are closed under all original set-valued functions, the COMPLETE generated boundary T=Cl(N(component(Source−S,x))) of any such component belongs to S∩K.

Thus the boundary-localization step required for selecting a proper one-sided inner piece can be reproved using **closedness + no-escape**, without already knowing K is a geometric minimal-separator piece. This is a possible alternative iteration invariant to explore.

## Critical remaining checks

- Prove no-escape is preserved by the literal full native source replacement `New = Q +_U E` when its complete complement map agrees with the old one, and when Q maps into A on its private vertices while U lies in S.
- Prove the rooted incompatibility profile for arbitrary closed contexts can continue to be transported with the same native nested-diagram congruence (existing generic module), and source support/retained root coordinates remain fixed (the merged one-step theorem provides the first such certificate).
- **Terminal flip issue:** the original global canonical relation indexes **genuine geometric forbidden pieces**. A closed no-escape context equivalent in rooted tests to a selected piece need not itself be a selected piece. Another legitimate selected witness or final geometric reconstruction is still needed.

Do not silently promote this alternative to unrestricted Claim 2, nor use an invalid weak target image quotient or assume intermediate A-minimality. Frozen manuscript prose unchanged; separate `#print axioms` and proof-root marker.
