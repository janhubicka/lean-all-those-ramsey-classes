import PartiteConstruction.Ramsey.ForbiddenFunctionsAllArity

/-!
# Track E: finite ordered functional structures are irreducible

The native strict-tree completion lemma for the maximal induced-trace
age assumes its constituent Base is irreducible in the FULL
functional-language sense: an embedded copy cannot cross the two
sides of any genuine full functional free amalgam.

After adding a distinguished external total linear order, this
hypothesis becomes automatic, regardless of whether the unordered
native or folded-tag reduct is irreducible. Any two distinct
vertices of an ordered copy are related by a positive comparison
in one direction. Such a comparison cannot cross the sides of a
full free amalgam. Consequently if one point is private to the
right side, every other point belongs to the right side as well.

This proof uses the actual two-place ORDER relation in
Structure.withLinearOrder, and full functional embeddings.
It neither changes the interpretation of old set-valued
functions nor assumes ordered strong amalgamation of any class.

The remaining step to apply the strict-tree lemma to ordered
maximal traces is to transport the finite native expanded
strong AP to compatible chosen external orders, and then solve
the actual sparse mixed selected-support attachment problem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Adjoining an actual external total linear order makes any
full functional structure irreducible in the whole ordered
relation/function language, for arbitrary native arities
including nullary symbols.

This is the exact irreducibility needed to localize a
full ordered Base-copy inside one free-amalgam source side. -/
theorem orderedFunctionalStructure_irreducible
    {V : Type} [LinearOrder V] (A : Structure L V) :
    A.withLinearOrder.Irreducible := by
  classical
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hfree e
  have pairRight
      (x y : V) (hxy : x < y)
      (hout :
        (¬ ∃ z : E, e x = iE z) ∨
        (¬ ∃ z : E, e y = iE z)) :
      (∃ z : F, e x = iF z) ∧
      (∃ z : F, e y = iF z) := by
    have hSource :
        A.withLinearOrder.rel (.inr ()) ![x, y] := hxy
    have hArg : e ∘ ![x, y] = ![e x, e y] := by
      funext i
      fin_cases i <;> rfl
    have hTarget : Csrc.rel (.inr ()) ![e x, e y] := by
      have he := (e.map_rel_iff (.inr ()) ![x, y]).mpr hSource
      rw [hArg] at he
      exact he
    rcases (hfree.rel_iff (.inr ()) ![e x, e y]).mp hTarget with
      ⟨args, _hArgs, hEq⟩ | ⟨args, _hArgs, hEq⟩
    · have hx : e x = iE (args 0) := by
        have h := congrFun hEq (0 : Fin 2)
        simpa using h
      have hy : e y = iE (args 1) := by
        have h := congrFun hEq (1 : Fin 2)
        simpa using h
      rcases hout with hNoX | hNoY
      · exact (hNoX ⟨args 0, hx⟩).elim
      · exact (hNoY ⟨args 1, hy⟩).elim
    · have hx : e x = iF (args 0) := by
        have h := congrFun hEq (0 : Fin 2)
        simpa using h
      have hy : e y = iF (args 1) := by
        have h := congrFun hEq (1 : Fin 2)
        simpa using h
      exact ⟨⟨args 0, hx⟩, ⟨args 1, hy⟩⟩
  by_cases hLeft : ∀ x : V, ∃ z : E, e x = iE z
  · exact Or.inl hLeft
  · right
    push_neg at hLeft
    obtain ⟨a, ha⟩ := hLeft
    intro b
    by_cases hab : a = b
    · subst b
      rcases hfree.covers (e a) with hSide | hSide
      · exact (ha hSide).elim
      · exact hSide
    · rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact (pairRight a b hlt (Or.inl ha)).2
      · exact (pairRight b a hgt (Or.inr ha)).1

end AllThoseRamseyClasses.Lifts
