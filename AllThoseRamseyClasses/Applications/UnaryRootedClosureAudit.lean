import Mathlib.Data.Set.Basic

/-!
# Rooted versus unrooted unary closure in the 2019 application

The printed direct proof of Theorem `thm:unaryfunc` says to identify
vertices with isomorphic 'vertex closures (including unary relations)'.
This needs to mean ROOTED closure (the isomorphism sends generator to
generator). The unrooted reading collapses even a two-cycle.

For a two-vertex unary algebra f(x)=not x, the closure of each vertex
is the SAME entire two-vertex induced algebra, with its same unary
label predicates. Therefore unrooted-closure equality already
identifies the two distinct generators. The quotient would fail
to embed the original two-cycle. Rooted closure retains the generator.

The checked regression below is only this ambiguity/counterexample.
It does not prove the repaired quotient construction, the full
finite unary Ramsey theorem or its countable-target extension.
-/

namespace AllThoseRamseyClasses.Applications.UnaryQuotient

/-- A generated unary-function substructure: intersection of all
subsets containing the root and closed under the two-cycle function. -/
def generatedClosure (x : Bool) : Set Bool :=
  { y | ∀ S : Set Bool, x ∈ S →
      (∀ z : Bool, z ∈ S → Bool.not z ∈ S) → y ∈ S }

/-- In a two-cycle, each individual generator closes to both points. -/
theorem generatedClosure_full (x y : Bool) :
    y ∈ generatedClosure x := by
  intro S hx hclosed
  by_cases heq : y = x
  · rw [heq]
    exact hx
  · have hy : y = Bool.not x := by
      cases x <;> cases y <;> simp_all
    rw [hy]
    exact hclosed x hx

/-- The two unrooted generated closures agree as exact induced
carriers. The identity also preserves any fixed unary labels. -/
theorem unrooted_two_cycle_closures_equal :
    generatedClosure false = generatedClosure true := by
  ext y
  constructor
  · intro _
    exact generatedClosure_full true y
  · intro _
    exact generatedClosure_full false y

/-- Thus quotienting generators by unrooted closure equality is
noninjective even inside the original two-vertex structure. -/
theorem naive_unrooted_closure_not_injective :
    ¬Function.Injective generatedClosure := by
  intro hinj
  have h : (false : Bool) = true :=
    hinj unrooted_two_cycle_closures_equal
  cases h

/-- A rooted closure remembers the vertex that generated the
induced substructure; this distinction is essential for quotients. -/
structure RootedClosure where
  carrier : Set Bool
  root : Bool

def rootedClosure (x : Bool) : RootedClosure :=
  ⟨generatedClosure x, x⟩

theorem rootedClosure_injective : Function.Injective rootedClosure := by
  intro x y h
  exact congrArg RootedClosure.root h

end AllThoseRamseyClasses.Applications.UnaryQuotient
