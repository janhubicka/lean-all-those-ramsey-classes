import AllThoseRamseyClasses.Applications.MetricCorrected2019SingletonHull
import AllThoseRamseyClasses.Applications.MetricNativeOneGeneratedUHulls

/-!
# Corrected (4b) on a genuinely U-closed canonical functional candidate

The revised 2019 Definition 2.17(4) EXPLICITLY requires the entire
candidate C to be U-closed. Only the small original induced subsets
tested by (4c) may fail to be U-closed. This distinction was missed in
the initial 29 October applications review.

Here we combine two already certified components:
* #702: corrected (4b) puts every one-generated U-hull of a
  genuinely U-closed candidate into K;
* #703: for the canonical positive-arity native function encoding,
  every one-generated U-hull is closed under ALL original functions.

For any chosen partial unary maps f_j whose DEFINED source values
are native function outputs of the canonical source, we therefore
derive closure of their one-generator U-hulls, rather than asking
for it as a separate global hypothesis.

Under an EXPLICIT K-to-Option normal-form semantic interpretation,
the corrected (4b) condition forces the two-step F_j normal form on
the entire original source, and hence the finite closed hull bound
m (|J|+1), without an assumed small hull.

This does NOT yet construct the needed interpretation of the concrete
2019 metric auxiliary class K, nor prove the printed exact (4c)
weak-subset completion/cycle compression/finite S-metric Ramsey arrow.
The paper's metric proof invokes the older locally finite subclass
theorem, so a direct bridge to that application is also required.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

universe u v

/-- In the canonical tagged native-function representation of an
arbitrary genuine singleton-valued source, corrected (4b)
immediately places EVERY original one-generated U-hull in K.
No bound on the hull size is assumed. -/
theorem canonicalSingleton_UHull_mem_of_corrected2019
    {L : Language.{u}} {V : Type v}
    (A : Structure L V)
    (hSingle : A.SingletonValued)
    (K : StructureClass.{u,v} (L := L.patternTag))
    (hCovered :
      CorrectedUIrreduciblesIn K L.patternClosureRules
        (patternTagExpansion A.patternGraph))
    (x : V) :
    K ((patternTagExpansion A.patternGraph).induce
      (UClosureHull L.patternClosureRules
        (patternTagExpansion A.patternGraph) {x})) := by
  exact corrected2019_singleton_Uhull_mem
    K L.patternClosureRules (patternTagExpansion A.patternGraph)
    (patternTagExpansion_isUClosed A hSingle) hCovered x

/-- Every defined selected f_j-value remains inside a generated
2019 U-hull, provided it is genuinely one of the original native
function outputs. No composition normal form is assumed here.
Repeated native input coordinates are allowed. -/
theorem canonicalNativeF_UHull_closed
    {L : Language.{u}} {V : Type v}
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (nativeSymbol : ℝ → L.FuncSymbol)
    (hNative : ∀ j ∈ J, ∀ x y : V,
      f j x = some y →
        y ∈ A.func (nativeSymbol j) (fun _ => x)) :
    ∀ a : V, ∀ j ∈ J,
      ∀ x ∈ UClosureHull L.patternClosureRules
        (patternTagExpansion A.patternGraph) {a},
      ∀ y : V,
        f j x = some y →
          y ∈ UClosureHull L.patternClosureRules
            (patternTagExpansion A.patternGraph) {a} := by
  intro a j hj x hx y hxy
  have hClosed :=
    nativeOneGenerated_UHull_isClosed A hPos a
  exact hClosed (nativeSymbol j) (fun _ => x)
    (fun _ => hx) (hNative j hj x y hxy)

/-- Exact corrected (4b) plus the CANONICAL native closure dictionary
transfers a K-piece composition identity to the original candidate
and yields a finite source hull WITHOUT circularly presupposing that
a small function-closed test exists.

The remaining hValidPiece is deliberately explicit: it asserts
that the concrete metric K-membership of each closed induced hull
forces the desired original Option-valued F_j composition law there.
This is the exact metric-class semantic bridge not yet certified. -/
theorem canonicalNativeMetricCandidate_finite_hull_of_corrected2019
    {L : Language.{u}} {V : Type v}
    (A : Structure L V) [Finite V]
    (hPos : L.PositiveFuncArity)
    (hSingle : A.SingletonValued)
    (K : StructureClass.{u,v} (L := L.patternTag))
    (hCovered :
      CorrectedUIrreduciblesIn K L.patternClosureRules
        (patternTagExpansion A.patternGraph))
    (J : Finset ℝ)
    (f : ℝ → V → Option V)
    (nativeSymbol : ℝ → L.FuncSymbol)
    (hNative : ∀ j ∈ J, ∀ x y : V,
      f j x = some y →
        y ∈ A.func (nativeSymbol j) (fun _ => x))
    (hValidPiece : ∀ T : Set V,
      K ((patternTagExpansion A.patternGraph).induce T) →
      ∀ j ∈ J, ∀ k ∈ J, ∀ x y z : V,
        x ∈ T → y ∈ T → z ∈ T →
        f j x = some y → f k y = some z →
        j < k ∧ f k x = some z)
    (seeds : List V) :
    ∃ D : Finset V,
      (∀ x ∈ seeds, x ∈ D) ∧
      D.card ≤ seeds.length * (J.card + 1) ∧
      MetricCandidateFinsetClosed J f D := by
  have hSourceClosed : IsUClosed L.patternClosureRules
      (patternTagExpansion A.patternGraph) :=
    patternTagExpansion_isUClosed A hSingle
  have hFrespects :=
    canonicalNativeF_UHull_closed A hPos J f nativeSymbol hNative
  exact corrected2019_candidate_finite_hull_of_singleton_hull
    K L.patternClosureRules (patternTagExpansion A.patternGraph)
    hSourceClosed hCovered J f hFrespects hValidPiece seeds

end AllThoseRamseyClasses.Applications.MetricSaturation
