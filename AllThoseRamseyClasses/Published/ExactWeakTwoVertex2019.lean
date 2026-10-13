import AllThoseRamseyClasses.Published.ClosedKRootTwoSide2019
import AllThoseRamseyClasses.Published.ExactWeakIntrinsicRankOne2019
import PartiteConstruction.Ramsey.ClosureWeakIrreducibleCoverage

/-!
# Every exact weak two-vertex test completes, without native HJ geometry

Let C be a finite U-closed Picture with the original closed
U-irreducible B-copy coverage. For a strong-amalgamation class K
of irreducibles, hereditary on closed substructures, every original
weak induced test on at most TWO vertices has a corrected K-completion.

The nonmaximal intrinsic-rank case is the existing rank-one theorem.
Ordinary irreducibles are covered through their actual ambient hull.
A remaining reducible test has a proper free decomposition whose
sides each have at most one vertex and whose common carrier is empty.
The empty root is U-closed because closure-rule roots are nonempty.
Its actual embedding into B, including all nullary data, is obtained
from the original coverage, not fabricated from an arbitrary empty map.
Closed rank-one completion of C also follows from that same coverage.
The checked closed-K-root two-side gluing theorem then applies to the
actual inclusions of both sides into C.

No native attachment, active-line, projected collision, old higher-rank,
or source-closedness hypothesis occurs. This is an absolute TWO-VERTEX
theorem, not completion of all possibly large rank-two closed hulls.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Every original exact weak test on at most two vertices has a
corrected completion from the ordinary closed Picture coverage and
class amalgamation hypotheses alone. -/
theorem inducedClosed2019_exact_weak_card_le_two_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VB : Type v} [Finite VC] [Finite VB]
    (C : RelStructure L VC) (B : RelStructure L VB)
    (hC : IsUClosed rules C) (hBK : K B)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (T : RelStructure L X),
      K T → T.Irreducible)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test → IsUIrreducible rules Test →
      Embedding Test C → Nonempty (Embedding Test B))
    (S : Finset VC) (hCard : S.card ≤ 2) :
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set VC)) := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  let Source := C.induce (↑S : Set VC)
  have hBIrr : B.Irreducible := hKIrr B hBK
  have hSourceCard : Fintype.card (↑S : Set VC) ≤ 2 := by
    simpa using hCard
  by_cases hRank : USize rules Source ≤ 1
  · exact inducedClosed2019_exact_weak_USize_le_one_completion
      C B hC hBK hBIrr hCover S hRank
  by_cases hIrred : Source.Irreducible
  · exact (inducedClosedKCompletion_iff_abstract_2019).mpr
      (weak_irreducible_completion_of_closed_coverage
        hC hBK hBIrr hCover (↑S : Set VC) hIrred)
  have hMax : USize rules Source = Fintype.card (↑S : Set VC) := by
    have hLe := USize_le_card rules Source
    omega
  obtain ⟨d⟩ := properFreeDecomposition_of_not_irreducible hIrred
  letI : Finite d.Left :=
    Finite.of_injective d.leftIn d.leftIn.injective
  letI : Finite d.Right :=
    Finite.of_injective d.rightIn d.rightIn.injective
  letI : Fintype d.Left := Fintype.ofFinite d.Left
  letI : Fintype d.Right := Fintype.ofFinite d.Right
  letI : Finite d.Common :=
    Finite.of_injective d.toLeft d.toLeft.injective
  have hLeftLt : Fintype.card d.Left < Fintype.card (↑S : Set VC) :=
    Fintype.card_lt_of_injective_not_surjective
      d.leftIn d.leftIn.injective d.leftProper
  have hRightLt : Fintype.card d.Right < Fintype.card (↑S : Set VC) :=
    Fintype.card_lt_of_injective_not_surjective
      d.rightIn d.rightIn.injective d.rightProper
  have hSizeL : Fintype.card d.Left ≤ 1 := by omega
  have hSizeR : Fintype.card d.Right ≤ 1 := by omega
  have hNoRoot : ∀ r : d.Common, False := by
    intro r
    apply d.leftProper
    intro z
    rcases d.free.covers z with ⟨x, hx⟩ | ⟨y, hy⟩
    · exact ⟨x, hx.symm⟩
    · have hFin : (Finset.univ : Finset d.Right).card ≤ 1 := by
        simpa using hSizeR
      have hyEq : y = d.toRight r :=
        Finset.card_le_one.mp hFin y (Finset.mem_univ y)
          (d.toRight r) (Finset.mem_univ (d.toRight r))
      refine ⟨d.toLeft r, ?_⟩
      calc
        d.leftIn (d.toLeft r) = d.rightIn (d.toRight r) :=
          (d.free.overlap (d.toLeft r) (d.toRight r)).mpr ⟨r, rfl, rfl⟩
        _ = d.rightIn y := congrArg d.rightIn hyEq.symm
        _ = z := hy.symm
  have hRootClosed : IsUClosed rules d.common := by
    intro rule _
    constructor
    · intro t _
      exact False.elim (hNoRoot
        (t ((⟨0, rule.rootPositive⟩ : Fin rule.rootSize).castLE
          rule.rootLE)))
    · intro e
      exact False.elim (hNoRoot (e ⟨0, rule.rootPositive⟩))
  have hRootIrred : d.common.Irreducible := by
    intro x y hxy
    exact (hNoRoot x).elim
  let inC : Embedding Source C := inclusion C (↑S : Set VC)
  let leftC : Embedding d.left C := inC.comp d.leftIn
  let rightC : Embedding d.right C := inC.comp d.rightIn
  obtain ⟨rootB⟩ := hCover d.common hRootClosed
    (hRootIrred.isUIrreducible rules) (leftC.comp d.toLeft)
  have hRootK : K d.common :=
    hHer d.common B hBK hRootClosed rootB
  have hOldRank : ∀ (T : Set VC) [Fintype T],
      IsUClosed rules (C.induce T) →
      USize rules (C.induce T) ≤ 1 →
      HasInducedClosedUKCompletion K rules (C.induce T) := by
    intro T _ hTClosed hTRank
    obtain ⟨e⟩ := hCover (C.induce T) hTClosed
      (hTClosed.uIrreducible_of_USize_le_one hTRank) (inclusion C T)
    exact (inducedClosedKCompletion_iff_abstract_2019).mpr
      ⟨VB, inferInstance, B, hBK, hBIrr,
        e, e.isClosedUHomomorphismEmbedding rules⟩
  exact inducedClosed2019_maximal_weak_two_old_maps_glue_of_closed_K_root
    d.free hMax C hC hStrong hHer hKIrr hRootK hRootClosed
    leftC rightC leftC.isHomomorphismEmbedding rightC.isHomomorphismEmbedding
    1 hSizeL hSizeR hOldRank

end AllThoseRamseyClasses.Published
