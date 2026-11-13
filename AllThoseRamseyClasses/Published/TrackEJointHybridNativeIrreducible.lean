import AllThoseRamseyClasses.Published.TrackEJointHybridCanonicalUClosed
import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import AllThoseRamseyClasses.Published.TrackENativeIrreducibleClosedCover
import PartiteConstruction.Ramsey.ClosureTaggedIrreducibility

/-!
# Track E2: native function-closedness and irreducibility in FULL JOINT hybrid tags

The genuine combined original-OLD-complete-mask / singleton-split
presentation has ONE fresh tagged closure description whose two
families are indexed by the ENTIRE induced base hybrid root. We
prove the missing exact source test dictionary:

* every U-substructure of the actual canonical JOINT tagged System
  is closed under every ORIGINAL multivalued native operation;
* a finite native irreducible partite System, with positive
  function input arities, is intrinsically U-irreducible as its
  canonical FULL JOINT tagged relational presentation.

The reverse closure implication constructs an actual fresh split
joint tag for EACH primitive function incidence y ∈ F(xs):
factor the repeated primitive inputs through their surjective
distinct-input equality pattern, pull back ALL hybrid relations
to that precise input root, and tag the existing output tuple.
The U-substructure rule forces precisely y into the SAME S.
Neither a closure hull nor new output/root vertices are introduced.

For U-irreducibility use the independently checked U-closed-cover
criterion for the actual JOINT source, and the merged native
irreducible closed-cover theorem. Every original relation and
every original function incidence is a genuine base-hybrid tuple,
so a two-sided tagged free cover is a native closed free cover.
This avoids FALSE ordinary Gaifman-clique irreducibility for native
unary chains.

The result applies to canonical FULL source/test presentations.
It does not assert the analogous claim for arbitrary induced tests
inside a NONCANONICAL sparse Ramsey Picture, or supply a complete
H-relative local map/strict mixed-root target. Those are distinct
remaining gates. Primitive nullary functions require a separate
positive-root reduction; the hypothesis is explicit.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- An EXACT relative U-substructure of the entire canonical
JOINT full-hybrid-root tagged presentation of a genuine native
partite System is closed under the ORIGINAL multivalued native
operations. Every output part is forced separately by its
full-hybrid-root split tag.

The source vertex set S is not enlarged. The implication uses
positive native function arities, but not finite carrier or
source fibre singletonness. -/
theorem nativeClosed_of_jointHybridUSubstructure
    (A : FunctionalPartite.System L Parts V) [Finite V]
    (hPos : L.PositiveFuncArity) (S : Set V)
    (hU : IsUSubstructure
      (L.splitMaskJointClosureRules Parts)
      (splitMaskJointRootExpansion A.splitMaskHybrid) S) :
    A.toStructure.IsClosed S := by
  classical
  intro F xs hx y hy
  obtain ⟨m, r, root, hr, hInj, hFact, _hExact⟩ :=
    exists_tuple_equality_pattern_exact xs
  have hmPos : 0 < m := by
    by_contra hn
    have hmZero : m = 0 := Nat.eq_zero_of_not_pos hn
    subst m
    exact Fin.elim0 (r ⟨0, hPos F⟩)
  let pat : Language.FunctionInputPattern L :=
    ⟨F, m, r, hr⟩
  let splitPat : Language.FunctionInputPattern (L.outputPartIndexed Parts) :=
    Language.splitMaskInputAtPart pat (A.part y)
  let G : RelStructure (L.splitMaskHybrid Parts) V :=
    A.splitMaskHybrid
  have hArgs : root ∘ r = xs := by
    funext i
    exact (hFact i).symm
  have hySplit :
      y ∈ A.splitOutputParts.toStructure.func
        splitPat.symbol (root ∘ splitPat.argMap) := by
    change y ∈ A.func F (root ∘ r) ∧ A.part y = A.part y
    exact ⟨by rw [hArgs]; exact hy, rfl⟩
  have hDomain :
      G.rel (Language.hybridSplitDomainSymbol splitPat) root := by
    change Function.Injective root ∧
      (A.splitOutputParts.toStructure.func
        splitPat.symbol (root ∘ splitPat.argMap)).Nonempty
    exact ⟨hInj, ⟨y, hySplit⟩⟩
  let rootHybrid : RelStructure (L.splitMaskHybrid Parts) (Fin m) :=
    { rel := fun R zs => G.rel R (root ∘ zs) }
  have hRootDomain :
      rootHybrid.rel (Language.hybridSplitDomainSymbol splitPat) id := by
    change G.rel (Language.hybridSplitDomainSymbol splitPat)
      root
    exact hDomain
  let tag : Language.SplitMaskFullRootPattern L Parts :=
    { input := splitPat
      positive := hmPos
      root := rootHybrid
      hasDomain := hRootDomain }
  let fullRoot : RelStructure.Embedding tag.root G :=
    { toFun := root
      injective := hInj
      map_rel_iff := by
        intro R zs
        rfl }
  let t : Fin (m + 1) → V :=
    Structure.funcTuple root y
  have hGraph :
      G.rel (Language.hybridSplitOutputSymbol splitPat) t := by
    change Function.Injective
        (fun i : Fin m => t i.castSucc) ∧
      t (Fin.last m) ∈
        A.splitOutputParts.toStructure.func splitPat.symbol
          ((fun i : Fin m => t i.castSucc) ∘ splitPat.argMap)
    simpa only [t, Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using
      (show Function.Injective root ∧
        y ∈ A.splitOutputParts.toStructure.func
          splitPat.symbol (root ∘ splitPat.argMap)
        from ⟨hInj, hySplit⟩)
  have hTag :
      (splitMaskJointRootExpansion G).rel (.inr (.inl tag)) t := by
    change G.rel (Language.hybridSplitOutputSymbol tag.input) t ∧
      ∃ e : RelStructure.Embedding tag.root G,
        ∀ i : Fin tag.input.rootSize, t i.castSucc = e i
    exact ⟨hGraph, fullRoot,
      fun i => Structure.funcTuple_castSucc root y i⟩
  have hPrefixIn : ∀ i : Fin m, t i.castSucc ∈ S := by
    intro i
    obtain ⟨k, hk⟩ := hr i
    have hmem : root i ∈ S := by
      rw [← hk, ← hFact k]
      exact hx k
    simpa only [t, Structure.funcTuple_castSucc] using hmem
  have hRule :
      tag.jointClosureRule ∈ L.splitMaskJointClosureRules Parts :=
    Or.inl ⟨tag, rfl⟩
  have hRootIn :
      ∀ i : Fin tag.jointClosureRule.rootSize,
        t (i.castLE tag.jointClosureRule.rootLE) ∈ S := by
    change ∀ i : Fin m, t (Fin.castSucc i) ∈ S
    exact hPrefixIn
  have hLast := hU tag.jointClosureRule
    hRule t hTag hRootIn (Fin.last m)
  simpa only [t, Structure.funcTuple_last] using hLast

/-- FINITE full native irreducible tests are intrinsically U-irreducible
in the ACTUAL canonical JOINT full-hybrid-root tagged language,
rather than merely in the old separate singleton-pattern tags.

The proof uses true native free-closed-cover irreducibility, not
ordinary Gaifman completeness. It leaves the exact source
vertices, parts, primitive functions and ALL original full
output-mask records unchanged. -/
theorem nativeIrreducible_canonicalJointHybrid_uIrreducible
    (A : FunctionalPartite.System L Parts V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (hIrred : A.toStructure.Irreducible) :
    IsUIrreducible (L.splitMaskJointClosureRules Parts)
      (splitMaskJointRootExpansion A.splitMaskHybrid) := by
  classical
  have hJointClosed :
      IsUClosed (L.splitMaskJointClosureRules Parts)
        (splitMaskJointRootExpansion A.splitMaskHybrid) :=
    A.splitMaskJointRoot_isUClosed
  apply hJointClosed.uIrreducible_of_closed_cover
  intro S T hUS hUT hCover hTuple
  have hS : A.toStructure.IsClosed S :=
    nativeClosed_of_jointHybridUSubstructure A hPos S hUS
  have hT : A.toStructure.IsClosed T :=
    nativeClosed_of_jointHybridUSubstructure A hPos T hUT
  apply nativeIrreducible_closedCover
    A.toStructure hIrred S T hS hT hCover
  · intro R xs hRel
    exact hTuple (.inl (.inl (.inl (.inl R)))) xs hRel
  · intro F xs y hy
    obtain ⟨m, r, root, hr, hInj, hFact, _hExact⟩ :=
      exists_tuple_equality_pattern_exact xs
    let pat : Language.FunctionInputPattern L :=
      ⟨F, m, r, hr⟩
    let splitPat :
        Language.FunctionInputPattern (L.outputPartIndexed Parts) :=
      Language.splitMaskInputAtPart pat (A.part y)
    let t : Fin (m + 1) → V :=
      Structure.funcTuple root y
    have hArgs : root ∘ r = xs := by
      funext i
      exact (hFact i).symm
    have hySplit :
        y ∈ A.splitOutputParts.toStructure.func
          splitPat.symbol (root ∘ splitPat.argMap) := by
      change y ∈ A.func F (root ∘ r) ∧ A.part y = A.part y
      exact ⟨by rw [hArgs]; exact hy, rfl⟩
    have hGraph :
        (splitMaskJointRootExpansion A.splitMaskHybrid).rel
          (.inl (Language.hybridSplitOutputSymbol splitPat)) t := by
      change Function.Injective
          (fun i : Fin m => t i.castSucc) ∧
        t (Fin.last m) ∈
          A.splitOutputParts.toStructure.func splitPat.symbol
            ((fun i : Fin m => t i.castSucc) ∘ splitPat.argMap)
      simpa only [t, Structure.funcTuple_castSucc,
        Structure.funcTuple_last] using
        (show Function.Injective root ∧
          y ∈ A.splitOutputParts.toStructure.func
            splitPat.symbol (root ∘ splitPat.argMap)
          from ⟨hInj, hySplit⟩)
    have hSide (Q : Set V)
        (hQ : ∀ k : Fin (m + 1), t k ∈ Q) :
        (∀ i, xs i ∈ Q) ∧ y ∈ Q := by
      constructor
      · intro i
        have hi := hQ (Fin.castSucc (r i))
        have ht : t (Fin.castSucc (r i)) = root (r i) :=
          Structure.funcTuple_castSucc root y (r i)
        rw [ht] at hi
        rw [hFact i]
        exact hi
      · have hi := hQ (Fin.last m)
        have ht : t (Fin.last m) = y :=
          Structure.funcTuple_last root y
        rw [ht] at hi
        exact hi
    rcases hTuple (.inl
        (Language.hybridSplitOutputSymbol splitPat))
        t hGraph with hLeft | hRight
    · exact Or.inl (hSide S hLeft)
    · exact Or.inr (hSide T hRight)

end AllThoseRamseyClasses.Published
