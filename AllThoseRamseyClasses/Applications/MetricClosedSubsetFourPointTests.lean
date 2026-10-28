import AllThoseRamseyClasses.Applications.MetricVaryingFourPointLocalWitnesses

/-!
# From a function-closed finite support completion to a four-point test

This is a concrete interface between an actual local completion of
a function-closed induced source subset and the independently proved
four-point path obstruction with target structures varying per test.

A support C includes the two candidate endpoints and their two
designated F_j representatives. The source partial F_j operation
restricts to C *exactly*, including undefinedness. A completion of
this subset is an injective map of C into a valid target with the
exact local metric edge and Option-valued functions preserved.

The theorem extends the map on C to an arbitrary total map on the
candidate by sending every vertex outside C to the image of the
first endpoint. This extension is NOT required to be globally
injective; it is injective on the four-point support, as required
by the already verified local-test lemma.

This removes a superficial 'global candidate map' hypothesis from
local tests, but DOES NOT assert that the original paper's weak
induced U-closed tests always yield a C satisfying this interface,
nor bound the cardinality of its FUNCTION-CLOSED hull. Those are
separate essential remaining printed-proof obligations.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- A local target completion of a function-closed subset C of the
candidate. Only the specified endpoint edge has to preserve its
distance; no metric condition on other candidate pairs is assumed.

The source partial F_j table restricts exactly to C, and the target
map commutes with these Option values on the whole C. This is
strictly stronger than arbitrary weak-induced completion, because
a weak induced subset may omit function values leaving C. -/
def MetricFourPointClosedSubsetCompletion
    (S : Set ℝ) {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (a b : A) : Prop :=
  ∃ (C : Set A) (fC : C → Option C)
    (V : Type u) (o : LinearOrder V)
    (dV : V → V → ℝ) (fV : V → Option V)
    (e : C → V),
    ({a, b, metricClosureRepresentative fA a,
      metricClosureRepresentative fA b} : Set A) ⊆ C ∧
    (∀ c : C, Option.map Subtype.val (fC c) = fA c.val) ∧
    MetricOn S dV ∧
    @MetricJumpClosureLaw V o dV fV j ∧
    Function.Injective e ∧
    (∀ c d : C, c.val = a → d.val = b →
      dV (e c) (e d) = dA a b) ∧
    (∀ c : C, fV (e c) = Option.map e (fC c))

/-- A genuine completion of a function-closed induced subset
produces exactly the four-point local test used in the short
path / long closing-edge obstruction. This is a statement
about the explicit subset completion above; it does NOT claim
the original weak-induced local-completion axiom supplies it. -/
theorem metricFourPointLocalTest_of_closedSubsetCompletion
    {S : Set ℝ} {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (a b : A)
    (hCompletion :
      MetricFourPointClosedSubsetCompletion S dA fA j a b) :
    MetricFourPointFunctionalLocalTest S dA fA j a b := by
  classical
  obtain ⟨C, fC, V, o, dV, fV, e,
    hSupport, hRestrict, hdV, hLaw, hInjE,
    hEdge, hFunctions⟩ := hCompletion
  have ha : a ∈ C := hSupport (by simp)
  have hb : b ∈ C := hSupport (by simp)
  let i : A → V :=
    fun x => if hx : x ∈ C then e ⟨x, hx⟩ else e ⟨a, ha⟩
  have hi (c : C) : i c.val = e c := by
    dsimp [i]
    simp only [dif_pos c.property]
  have hOption (c : C) :
      fV (i c.val) = Option.map i (fA c.val) := by
    calc
      fV (i c.val) = fV (e c) := by rw [hi c]
      _ = Option.map e (fC c) := hFunctions c
      _ = Option.map i (fA c.val) := by
        rw [← hRestrict c]
        cases h : fC c with
        | none => simp [h]
        | some z =>
            simp only [h, Option.map_some]
            exact congrArg (fun v : V => (some v : Option V)) (hi z).symm
  refine ⟨V, o, dV, fV, i, hdV, hLaw, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hxC : x ∈ C := hSupport hx
    have hyC : y ∈ C := hSupport hy
    have hE : e ⟨x, hxC⟩ = e ⟨y, hyC⟩ := by
      calc
        e ⟨x, hxC⟩ = i x := (hi ⟨x, hxC⟩).symm
        _ = i y := hxy
        _ = e ⟨y, hyC⟩ := hi ⟨y, hyC⟩
    exact congrArg Subtype.val (hInjE hE)
  · calc
      dV (i a) (i b) = dV (e ⟨a, ha⟩) (e ⟨b, hb⟩) := by
        rw [hi ⟨a, ha⟩, hi ⟨b, hb⟩]
      _ = dA a b := hEdge ⟨a, ha⟩ ⟨b, hb⟩ rfl rfl
  · exact hOption ⟨a, ha⟩
  · exact hOption ⟨b, hb⟩

/-- Even completely different closed-subset targets on different
short edges cannot coexist with a locally completed long closing
edge. Unlike a global candidate embedding, each local map here
exists ONLY on its chosen function-closed subset. -/
theorem metricShortPath_longEdge_obstruction_of_closedSubsetCompletions
    {S : Set ℝ}
    (hpos : Positive S) (hS : WellDefined S)
    {A : Type u}
    (dA : A → A → ℝ) (fA : A → Option A)
    (j : ℝ) (hj : Jump S j)
    (hLocal : ∀ a b : A, dA a b ≤ j →
      MetricFourPointClosedSubsetCompletion S dA fA j a b)
    (x y : A)
    (hPath : Relation.ReflTransGen
      (fun a b : A => dA a b ≤ j) x y)
    (hLong : j < dA x y)
    (hClosing :
      MetricFourPointClosedSubsetCompletion S dA fA j x y) :
    False := by
  apply metricShortPath_longEdge_obstruction_of_varying_fourPointTests
    hpos hS dA fA j hj
    (fun a b hab =>
      metricFourPointLocalTest_of_closedSubsetCompletion
        dA fA j a b (hLocal a b hab))
    x y hPath hLong
  exact metricFourPointLocalTest_of_closedSubsetCompletion
    dA fA j x y hClosing

end AllThoseRamseyClasses.Applications.MetricSaturation
