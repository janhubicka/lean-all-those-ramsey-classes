import AllThoseRamseyClasses.Lifts.SelectedSymbolReachableProfile
import AllThoseRamseyClasses.Lifts.Claim2SelectedSymbolDescentProfile

-- Symbol-preserving paths recover all source-root data without
-- requiring terminality, rank decrease, or positive successor existence.
#check AllThoseRamseyClasses.Lifts.selectedSymbol_reachable_preserves_width_root_allTests
#print axioms AllThoseRamseyClasses.Lifts.selectedSymbol_reachable_preserves_width_root_allTests

-- Valid-state form does not impose symbol preservation on invalid states.
#check AllThoseRamseyClasses.Lifts.selectedSymbol_valid_reachable_preserves_width_root_allTests
#print axioms AllThoseRamseyClasses.Lifts.selectedSymbol_valid_reachable_preserves_width_root_allTests

-- The historical terminal API is preserved after factoring its
-- duplicated path induction into the reusable valid-state theorem.
#check AllThoseRamseyClasses.Lifts.claim2_selectedSymbol_terminal_preserves_width_root_allTests
#print axioms AllThoseRamseyClasses.Lifts.claim2_selectedSymbol_terminal_preserves_width_root_allTests
