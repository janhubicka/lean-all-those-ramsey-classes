# Track C: old opposite boundary could rule out split-root capture for ALL widths

15 November 2026. New proposed actual original functional-source
geometric theorem. NOT YET VALIDATED: exact-head Lean/axioms/
no-admission/integrity/inventory CI must pass before any claim of
resolved higher-width capture. Frozen 2019 manuscript untouched.

Let P and d be true minimal FUNCTION-CLOSED separators of ONE
original native functional source, with the entire NEW closed
root d.root inside the actual OLD selected P piece
P.root ∪ component(P.left).

Denote the OLD opposite component C_old = component(P.right)
after deleting P.root. Because it is disjoint from BOTH the
old root and the old selected P.left component, it avoids
the entire new cut d.root. Thus C_old lies inside ONE
new-cut component C_new containing P.right.

The union d.root ∪ C_new is FULLY FUNCTION-CLOSED, by the
verified component-union closure lemma. Every external Gaifman
neighbor of C_old is either in d.root or belongs to C_new,
since C_old⊆C_new and C_new is an entire new-cut component.
Hence the generated closure of C_old's boundary lies inside
d.root ∪ C_new.

But MINIMALITY of the OLD P separator certifies the entire
old root P.root is EXACTLY the function closure of the
Gaifman neighborhood of C_old (the right/opposite boundary
identity). Consequently:

  P.root ⊆ d.root ∪ C_new.

In particular every old P-root source vertex outside d.root
is reached from P.right along an actual source Gaifman path
AVOIDING the full new d.root. This is the first proposed
theorem
`geometric_oldRoot_reachable_from_oldOpposite_after_innerCut`.

If d.left selected component captured old P-root vertex r
and the OPPOSITE d.right component captured another old
P-root vertex s, then r and s both lie in C_new and are
connected by paths avoiding d.root through P.right.
This yields an actual ReachOutside path from d.left to
d.right, CONTRADICTING d's genuine minimal-separator
disconnection. Proposed second theorem
`geometric_no_twoSidedOldRootCapture_of_newRoot_inside_oldPiece`
rules out this split-source-root capture for ARBITRARY old
root width n, with NO weak-map injection, no forbidden-family
specific assumption, no original A-minimality, no source
image quotient and no arity restriction.

**Adversarial caveat:** The argument relies on the actual
FULL functional closure of the old opposite boundary, not
merely graph adjacency to every old root. The critical
Lean proof obligations are source path transport avoiding
the NEW closed cut, full closedness of its root+opposite
component union, and exact right boundary closure equation.
If the proposed source-path proof fails at those hypotheses,
the higher-width case remains open. Do not update the frozen
circulation manuscript or remove capture TODOs based only
on this draft.

Two named Lean #print axioms checks, protected active root.
