# Track C: all small relatively closed cuts of a bad weak test have reducible roots

12 November 2026. **Draft, dependent on #1053 and #1052.**
The printed Nešetřil programme survey is frozen and unchanged.

The new Lean theorem `genuineTagged2019_badWeak_relativeFreeCut_root_reducible`
takes ONE exact finite weak source `C.induce S` which has no genuine
H-relative completion, together with ANY of its actual free
decompositions whose side ranges are relatively U-closed and whose
side vertex counts are at most j. Under corrected (4b), H strong
amalgamation, ordinary irreducibility of canonical K(H) targets, and
the explicit closed U-generating-rank-j completion premise, the
common root cannot be ordinarily irreducible.

This sharpens the necessary-obstruction diagnosis: it is not merely
the one decomposition selected by the weak-rank dichotomy that needs
a noncanonical boundary. **Every** eligible small relative cut has
an ordinary-reducible root. The proof is the contrapositive of #1053's
exact-source ambient-hull gluing theorem. No stronger class-locality
or boundary hypothesis is inferred.

Critical outstanding inputs for the complete survey proof:

1. Supply the actual Hales–Jewett/iterated-partite history that avoids
   or repairs these ordinary-reducible roots. A root merely embedded
   in an arbitrary ordinary-irreducible B is not necessarily
   irreducible itself for higher-arity relations; a hereditary
   irreducibility certificate or a protected CLOSED canonical
   boundary is needed.
2. Justify the closed **U-generating-rank** invariant from the
   construction at the survey's fixed original vertex cutoff.
   U-closure hulls of j seeds may have many more than j vertices,
   so the printed n-vertex hypothesis is not automatically enough.

This module leaves the exact OLD source carrier, whole domain masks,
and frozen TeX untouched. It does not prove the unrestricted rank
increment. Exact-head full Lean, inventory, axiom and admission checks
are required before merge.
