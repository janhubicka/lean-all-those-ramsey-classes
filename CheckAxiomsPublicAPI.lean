import AllThoseRamseyClasses.PublicAPI

/-! Machine-checked inventory of researcher-facing declarations.
Each #check is a compile-time assertion that the cited name exists
through the single stable public import. #print axioms audits the
new wrapper and its principal theorem dependencies. -/

-- Core relational language / embeddings / Ramsey arrows.
#check StructuralRamsey.RelLanguage
#check StructuralRamsey.RelStructure
#check StructuralRamsey.RelStructure.Embedding
#check StructuralRamsey.RelStructure.Irreducible
#check StructuralRamsey.RelStructure.IsHomomorphismEmbedding
#check StructuralRamsey.Arrow
#check StructuralRamsey.RelStructure.FiniteRamseyClass

-- Original closure-description definitions.
#check StructuralRamsey.RelStructure.ClosureRule
#check StructuralRamsey.RelStructure.ClosureDescription
#check StructuralRamsey.RelStructure.IsUClosed
#check StructuralRamsey.RelStructure.IsUSemiClosed
#check StructuralRamsey.RelStructure.IsUSubstructure
#check StructuralRamsey.RelStructure.UClosureHull
#check StructuralRamsey.RelStructure.USize
#check StructuralRamsey.RelStructure.IsUIrreducible
#check StructuralRamsey.RelStructure.IsUHomomorphismEmbedding
#check AllThoseRamseyClasses.Published.lemma_2_23_one

-- Coordinated correction of the paper's exact induced-test semantics.
#check AllThoseRamseyClasses.Published.IsInducedClosedUHomomorphismEmbedding
#check AllThoseRamseyClasses.Published.HasInducedClosedUKCompletion
#check AllThoseRamseyClasses.Published.InducedClosedULocalCompletionAt
#check AllThoseRamseyClasses.Published.InducedClosed2019Hereditary
#check AllThoseRamseyClasses.Published.InducedClosed2019MultiamalgamationClass
#check AllThoseRamseyClasses.Published.IsomorphismClosed2019
#check AllThoseRamseyClasses.Published.IsCoordinated2019MultiamalgamationClass
#check StructuralRamsey.RelStructure.HasFiniteStrongAmalgamation
#check StructuralRamsey.RelStructure.ClosedUMultiamalgamationClass

-- Fully proved main theorem and constructive supporting statements.
#check AllThoseRamseyClasses.Published.coordinated2019_theorem218
#check AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening
#check AllThoseRamseyClasses.Published.coordinated2019_profile_sparse_witness
#check AllThoseRamseyClasses.Published.lemma_2_28_coordinated_unrestricted_induced
#check AllThoseRamseyClasses.Published.lemma_2_29_coordinated_induced_full
#check AllThoseRamseyClasses.Published.IsCoordinated2019MultiamalgamationClass.toAbstract
#check AllThoseRamseyClasses.Published.coordinated2019_to_abstract_closed_class

-- The separate verified ordered partial-single-valued-function result.
#check StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions

#print axioms AllThoseRamseyClasses.Published.coordinated2019_theorem218
#print axioms AllThoseRamseyClasses.Published.coordinated2019_ramsey_by_profile_sparsening
#print axioms AllThoseRamseyClasses.Published.lemma_2_28_coordinated_unrestricted_induced
#print axioms AllThoseRamseyClasses.Published.lemma_2_29_coordinated_induced_full
#print axioms StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions
