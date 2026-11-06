import AllThoseRamseyClasses.Published.FunctionalWithParts2019RelativeKCompletion
import PartiteConstruction.Functional.WholeMaskCoveredUnaryPart2019
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls

/-!
# Track C: genuine part labels from the ACTUAL corrected (4b) antecedent

Earlier normalization of an arbitrary 2019 tagged candidate C needed
fixed canonical B-copy coverage. The local-finiteness axiom does NOT
have that antecedent: its corrected clause (4b) only says each closed
U-irreducible exact induced substructure belongs to K.

Here we obtain an important first piece of normalization *directly*
from that actual clause. A singleton is ordinarily irreducible; its
ambient U-closure hull is U-closed and U-irreducible. Therefore the
whole hull is a canonical tagged member of K. The same-carrier
canonical witness forces exactly one old unary part predicate at
the original singleton, without enlarging any local weak test.

The argument requires no globally fixed B and no invented
coherence assumption. It does NOT yet prove complete-function-value
uniqueness, OLD tag normality, or the full class-local implication.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Corrected clause (4b) is already enough to force one and
only one vertex part label at every point of a U-closed candidate.
The local canonical witness may depend on the vertex: no universal
Base B is assumed. -/
theorem genuineTagged2019_correctedCovered_vertexPart_existsUnique
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (x : V) :
    ∃! p : Parts, WholeMaskVertexPartHolds C x p := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let S : Set V := {x}
  let Hull : Set V := UClosureHull rules C S
  have hSingletonIrred : (C.induce S).Irreducible := by
    intro y z hNe
    have hEq : y = z := by
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp y.2).trans
        (Set.mem_singleton_iff.mp z.2).symm
    exact (hNe hEq).elim
  have hHullClosed : IsUClosed rules (C.induce Hull) :=
    hClosed.induce_UClosureHull S
  have hHullIrred : IsUIrreducible rules (C.induce Hull) :=
    hClosed.irreducibleSeed_hull_isUIrreducible S hSingletonIrred
  have hHullK : canonicalGenuineTagged2019Class H (C.induce Hull) :=
    hCovered Hull hHullClosed hHullIrred
  obtain ⟨_, Base, basePart, _, _, hCanonical⟩ := hHullK
  let vertex : Hull :=
    ⟨x, subset_UClosureHull rules C S (Set.mem_singleton x)⟩
  let p : Parts := basePart vertex
  have hPart : WholeMaskVertexPartHolds C x p := by
    have hInHull : (C.induce Hull).rel
        (.inl (.inl (.inr p)))
        (fun _ : Fin 1 => vertex) := by
      rw [hCanonical]
      rfl
    exact hInHull
  refine ⟨p, hPart, ?_⟩
  intro q hq
  have hInHull : (C.induce Hull).rel
      (.inl (.inl (.inr q)))
      (fun _ : Fin 1 => vertex) := hq
  rw [hCanonical] at hInHull
  exact hInHull.symm

/-- A canonical part map can be chosen for each vertex of a genuine
(4b)-covered U-closed candidate. It is an honest existing unary
part label, rather than a new unconstrained decoration. -/
noncomputable def genuineTagged2019_correctedCoveredPart
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (x : V) : Parts :=
  Classical.choose
    (genuineTagged2019_correctedCovered_vertexPart_existsUnique
      H C hClosed hCovered x)

theorem genuineTagged2019_correctedCoveredPart_holds
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (x : V) :
    WholeMaskVertexPartHolds C x
      (genuineTagged2019_correctedCoveredPart
        H C hClosed hCovered x) :=
  (Classical.choose_spec
    (genuineTagged2019_correctedCovered_vertexPart_existsUnique
      H C hClosed hCovered x)).1

end AllThoseRamseyClasses.Published
