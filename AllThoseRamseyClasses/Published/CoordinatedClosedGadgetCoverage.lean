import AllThoseRamseyClasses.Published.CoordinatedAllBlockCliques
import AllThoseRamseyClasses.Published.CoordinatedCycleProtectedReduction

/-!
# Discharge the all-cliques coverage premise for the 2019 repair

This file closes the first of the two clearly displayed assumptions
from CoordinatedCycleProtectedReduction. The independent theorem
cycle_block_clique_in_gadget shows that EVERY clique in the actual
matching-block graph is in one induced B0-gadget, including empty
and singleton cliques. No extra assumption on a test is needed.

Consequently the proposed (4a) and (4b) follow from only the
remaining explicitly stated universal *induced B0-gadget template*
obligation. The actual gadget-template family and weak exact-test
(4c) completions are not asserted here.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- The all-cliques combinatorial obligation holds in every actual C_k. -/
theorem cycle_blockCliqueCoverage (k : ℕ) :
    CycleBlockCliqueCoverage k :=
  cycle_block_clique_in_gadget k

/-- Uniform closed-test membership (4b) depends ONLY on constructing
genuine induced B0 templates, with block coverage, for each gadget. -/
theorem cycle_closedUIrreduciblesIn_of_induced_gadgets
    (k : ℕ) (hGadgets : CycleInducedGadgetTemplates k) :
    ClosedUIrreduciblesIn finitePairedClass mateRules
      (cycleGadgetWitness k) :=
  cycle_closedUIrreduciblesIn_of_gadgets
    k (cycle_blockCliqueCoverage k) hGadgets

/-- Uniform protected control homomorphism (4a) likewise needs only
actual induced B0 gadget templates; the positive map and its clique
localization have already been proved. -/
theorem cycle_control_closedUHomomorphismEmbedding_of_induced_gadgets
    (k : ℕ) (hGadgets : CycleInducedGadgetTemplates k) :
    IsClosedUHomomorphismEmbedding mateRules
      (cycleGadgetWitness k) CycleControlC0
      (cycleControlVertex k) :=
  cycle_control_closedUHomomorphismEmbedding_of_gadgets
    k (cycle_blockCliqueCoverage k) hGadgets

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
