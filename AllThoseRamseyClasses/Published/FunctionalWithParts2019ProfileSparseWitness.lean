import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
import PartiteConstruction.Functional.WholeMaskWithPartsClosedRank2019

/-!
# Corrected Appendix A: two-pass 2019 sparsening with genuine partial functions

This is a direct specialization of the ALREADY VERIFIED coordinated
2019 two-pass proof, not a new Hales-Jewett rank induction. We first
expand the genuine Option(Set) source language by the actual unary
VERTEX-part predicates, then encode the independent whole-value
function domains, complete output masks and full 2019 closure-root
tags. The original vertices, parts and all Option(Set) function
values remain unchanged.

The source is U-CLOSED and every exact whole-fibre weak test has the
SAME intrinsic generator rank as USize of the ambient full-root
tagged graph induced on its exact carrier.

The verified generated-profile construction then produces:
* a closed initial Ramsey picture;
* generated-closure profiles recording whole closed B-boundaries;
* relational strict-tree sparsening;
* a SECOND tagged closed partite pass;
* local completions of every original exact weak vertex test.

Its sparse relational witness therefore exists without the false
intermediate maximal-mixed strict FUNCTIONAL B-tree extension premise.

This is not yet the COMPLETE functional Ramsey theorem: the class K
of completed canonical function structures and the final recovery of
part-preserving full function embeddings / copywise completions still
require their own transfer proofs. No arbitrary intermediate
relational target is claimed to decode to functions.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The checked complete-mask U-closed source encoding with parts
present as actual unary primitive relations, not external data. -/
abbrev genuineWithPartsTagged2019
    {X : Type w}
    (A : PartialSetStructure L X) (part : X → Parts) :
    RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) X :=
  withPartsWholeMaskTag A part

/-- Exact functional weak generator rank agrees with induced-ambient
2019 USize even AFTER adding the vertex part predicates. -/
theorem genuineWithParts2019_weakRank
    {X : Type w} [Finite X]
    (A : PartialSetStructure L X) (part : X → Parts)
    (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal A part)
    (S : Set X) [Fintype S] (n : ℕ) :
    (wholeWeakInduce A S).GeneratedByAtMost n ↔
      USize ((L.withParts Parts).wholeMaskClosureRules Parts)
        ((genuineWithPartsTagged2019 A part).induce S) ≤ n :=
  A.withPartsWholeMaskTag_exactWeakUSize
    part hPos hTrans S n

/-- The already proved coordinated 2019 relational sparse-witness
constructor, specialized to genuine partial function SOURCES in the
correct part-labelled full-root complete-mask language.

No assumed native maximal-mixed functional B-tree completion, no
additional generators and no enlargement of weak source tests. -/
theorem genuineWithParts2019_profile_sparse_witness
    {X Y Z : Type w}
    [Finite X] [Finite Y] [Finite Z]
    (A : PartialSetStructure L X) (partA : X → Parts)
    (B : PartialSetStructure L Y) (partB : Y → Parts)
    (C0 : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Z)
    (hTransA : FibreTransversal A partA)
    (hTransB : FibreTransversal B partB)
    {K : StructureClass (L := (L.withParts Parts).wholeMaskTagLanguage Parts)}
    (hBK : K (genuineWithPartsTagged2019 B partB))
    (hClosed : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) E)
    (hHer : ClosedUHereditary K
      ((L.withParts Parts).wholeMaskClosureRules Parts))
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {T : Type w}
      (E : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) T),
      K E → E.Irreducible)
    (n : ℕ) (κ : Type) [Fintype κ] [Nonempty κ]
    (hArrow0 : StructuralRamsey.Arrow
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB) C0 κ) :
    HasInducedClosed2019SparseWitness K
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (genuineWithPartsTagged2019 A partA)
      (genuineWithPartsTagged2019 B partB) C0 n κ := by
  exact coordinated2019_profile_sparse_witness
    (genuineWithPartsTagged2019 A partA)
    (genuineWithPartsTagged2019 B partB)
    C0
    (A.withPartsWholeMaskTag_isUClosed partA hTransA)
    (B.withPartsWholeMaskTag_isUClosed partB hTransB)
    hBK hClosed hHer hStrong hKIrr n κ hArrow0

end AllThoseRamseyClasses.Published
