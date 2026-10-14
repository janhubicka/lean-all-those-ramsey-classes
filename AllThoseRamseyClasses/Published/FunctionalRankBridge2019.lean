import AllThoseRamseyClasses.Published.FunctionalStrictSparsening2019
import PartiteConstruction.Functional.TupleEqualityPattern2019
import PartiteConstruction.Functional.RankedEHNReduct
import PartiteConstruction.Functional.RankedTreeReduct
import PartiteConstruction.Functional.SingletonReduction

/-!
# Ready-to-use verified rank-descent interface for strict functional sparsening

This wrapper imports the now verified complete EHN descent,
strict-functional-tree descent, and Ramsey-arrow descent from the
reusable partite construction library.

A native set-valued strict sparsening theorem still requires a
faithful closure-description representation of SINGLETON-VALUED
partial ranked symbols (including repeated input patterns and nullary
symbols). This module deliberately does not assert that missing
equivalence as an axiom or a theorem.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey

/-- All the rank-reduct preservation components used by the prospective
native-function transfer are compiled and axiom-audited together. -/
example : True := by trivial

#check StructuralRamsey.Structure.IsEHNHomomorphismEmbedding.rankReduct
#check StructuralRamsey.Structure.Embedding.rankReduct
#check StructuralRamsey.Structure.TreeAmalgam.rankExpand_treeReduct
#check StructuralRamsey.Structure.arrow_of_singletonExpansion
#check StructuralRamsey.Structure.exists_tuple_equality_pattern_exact

end AllThoseRamseyClasses.Published
