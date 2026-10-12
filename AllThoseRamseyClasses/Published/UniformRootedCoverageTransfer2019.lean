import AllThoseRamseyClasses.Published.ClosedSingletonKAnchor2019
import AllThoseRamseyClasses.Published.UniformKRootedWeakSize2019
import AllThoseRamseyClasses.Published.VariableKRootWeakCompletion2019

/-!
# Genuine B-coverage + uniform rooted W_j^K gives weak j+1 completion

The three independently CI-green repaired 2019 ingredients are now:

1. Every vertex of a U-closed old Picture D whose closed
   U-irreducibles embed into a fixed B∈K has a genuine CLOSED
   U-irreducible K singleton-generated root Q_x embedded in D
   (merged PR #163, closed heredity used).
2. The uniform rooted weak-size invariant W_j^K(D) explicitly
   completes every exact weak old j-vertex set together with ANY
   embedded closed U-irreducible K-root Q (merged PR #164).
3. A protected map of a nonempty exact weak source of ≤j+1 vertices
   into a Picture having those two properties yields a genuine
   corrected K-completion (merged PR #165). The root Q may vary
   with the selected source vertex.

Here we combine these REAL declarations, eliminating the previously
abstract "all old vertices K-anchored" premise from #165.

The old target D need not be in K or itself K-completable.
No fixed-A vertex cover, old R_j invariant, closure of tested
weak source, global injection, or root vertex count is assumed.

One paper-faithful corollary applies the combination to a finite
original weak test C|S of ANY Picture C with a corrected protected
projection directly into D, without requiring C|S U-closed.

Crucial LIMITATION: in the true transverse native Hales--Jewett
successor Picture, a protected global map C->OLD D need not exist!
Usually there is only a map to the temporary native ATTACHMENT,
which may not be closed. The native multi-line root and successor
construction remain OPEN. This theorem must not be promoted to
a proof of unrestricted Lemma 2.30 or repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A nonempty exact weak source of ≤j+1 vertices which has a
corrected protected map into a CLOSED, B-covered old Picture
satisfying uniform rooted W_j^K has an actual K-completion.

The singleton-generated K-anchor is CONSTRUCTED from the actual
closed-irreducible B-coverage, not a free extra assumption. -/
theorem inducedClosed2019_weak_jplus1_of_uniform_rooted_and_coverage
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U VD VB : Type v}
    [Fintype U] [Nonempty U] [Finite VD]
    (Source : RelStructure L U)
    (D : RelStructure L VD)
    (B : RelStructure L VB)
    (hD : IsUClosed rules D)
    (hBK : K B)
    (hHer : ClosedUHereditary K rules)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test D →
      Nonempty (Embedding Test B))
    (p : U → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source D p)
    (j : ℕ) (hCard : Fintype.card U ≤ j+1)
    (hUniform : Has2019UniformKRootedWeakSize K rules D j) :
    HasInducedClosedUKCompletion K rules Source := by
  have hAnchor : ∀ y : VD,
      ∃ S : Set VD, y ∈ S ∧
        IsUClosed rules (D.induce S) ∧
        IsUIrreducible rules (D.induce S) ∧
        K (D.induce S) :=
    native2019_closed_picture_vertex_has_K_singleton_anchor
      D B hD hBK hHer hCover
  exact inducedClosed2019_weaksize_completion_of_variable_K_anchor
    Source D p hp j hCard hAnchor hUniform

/-- Apply the genuine variable-root completion to any ORIGINAL
nonempty exact weak induced S in a finite source Picture C carrying
a corrected protected map to the old CLOSED, B-covered D.

The weak source C|S is never replaced by its ambient closure;
the full source C need not be U-closed for this conditional map
transfer, although the actual 2019 Pictures are U-closed. -/
theorem inducedClosed2019_exact_weak_test_of_uniform_rooted_old
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD VB : Type v}
    [Finite VC] [Finite VD]
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (B : RelStructure L VB)
    (hD : IsUClosed rules D)
    (hBK : K B)
    (hHer : ClosedUHereditary K rules)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test D →
      Nonempty (Embedding Test B))
    (p : VC → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules C D p)
    (j : ℕ)
    (hUniform : Has2019UniformKRootedWeakSize K rules D j)
    (S : Finset VC) (hS : S.Nonempty)
    (hCard : S.card ≤ j+1) :
    HasInducedClosedUKCompletion K rules
      (C.induce (↑S : Set VC)) := by
  classical
  letI : Fintype VC := Fintype.ofFinite VC
  letI : Nonempty (↑S : Set VC) := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨⟨x, hx⟩⟩
  have hpAbstract : IsClosedUHomomorphismEmbedding rules C D p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hRestricted : IsInducedClosedUHomomorphismEmbedding rules
      (C.induce (↑S : Set VC)) D
      (fun x : (↑S : Set VC) => p x.1) :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (hpAbstract.precomp_embedding (inclusion C (↑S : Set VC)))
  have hCard' : Fintype.card (↑S : Set VC) ≤ j+1 := by
    simpa using hCard
  exact inducedClosed2019_weak_jplus1_of_uniform_rooted_and_coverage
    (C.induce (↑S : Set VC)) D B
    hD hBK hHer hCover
    (fun x : (↑S : Set VC) => p x.1) hRestricted
    j hCard' hUniform

end AllThoseRamseyClasses.Published
