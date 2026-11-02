import PartiteConstruction.Structure.Order
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Track E: every FULLY ordered functional structure is irreducible

The native finite-family enlarged witness Bbar need not be
irreducible in its original relation/function signature. In
particular, this is false already for a two-point edgeless
structure in the empty forbidden family.

However, the FULLY ordered expansion Bbar.withLinearOrder
is always irreducible in the genuine functional language
which includes the distinguished strict total order relation.

Indeed, if an embedded copy of Bbar crossed a full functional
free amalgam from the two sides, choose one image vertex
outside the first side. Every other image vertex is comparable
with it via the embedded total order, and every such ordered
relation must lie entirely in one source side. It therefore
also lies on the second side; the whole copy is localized
there. This uses only full relation reflection and the
actual free amalgam's relation-iff law.

This handles arbitrary old relations and SET-VALUED functions,
including nullary input arities; it is NOT a replacement for
the still required strong amalgamation of ordered age members.
That ordered-amalgamation/order-completion bridge remains a
separate structural obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A FULL strict linear ordering makes any functional
structure irreducible with respect to full functional
free amalgamation (regardless of its native irreducibility).

The finite carrier and native function arities are unrestricted.
Only the completeness of the newly added order relation is used. -/
theorem functionalWithLinearOrder_irreducible
    {V : Type} [LinearOrder V] (B : Structure L V) :
    B.withLinearOrder.Irreducible := by
  intro H E F C Dsrc Esrc Fsrc Csrc sE sF iE iF hFree e
  classical
  by_cases hLeft : ∀ x : V, ∃ a : E, e x = iE a
  · exact Or.inl hLeft
  · right
    push_neg at hLeft
    obtain ⟨x₀, hx₀⟩ := hLeft
    have inRight (x : V) (hOrder : x₀ < x) :
        ∃ b : F, e x = iF b := by
      have hRel :
          Csrc.rel (.inr ()) ![e x₀, e x] := by
        have he := (e.map_rel_iff (.inr ()) ![x₀, x]).mpr hOrder
        have hargs : e ∘ ![x₀, x] = ![e x₀, e x] := by
          funext k
          fin_cases k <;> rfl
        rw [hargs] at he
        exact he
      rcases (hFree.rel_iff (.inr ()) ![e x₀, e x]).mp hRel with
        ⟨xs, _, hxs⟩ | ⟨xs, _, hxs⟩
      · exfalso
        apply hx₀
        exact ⟨xs 0, by
          have h0 := congrFun hxs (0 : Fin 2)
          simpa using h0⟩
      · exact ⟨xs 1, by
          have h1 := congrFun hxs (1 : Fin 2)
          simpa using h1⟩
    have inRight_rev (x : V) (hOrder : x < x₀) :
        ∃ b : F, e x = iF b := by
      have hRel :
          Csrc.rel (.inr ()) ![e x, e x₀] := by
        have he := (e.map_rel_iff (.inr ()) ![x, x₀]).mpr hOrder
        have hargs : e ∘ ![x, x₀] = ![e x, e x₀] := by
          funext k
          fin_cases k <;> rfl
        rw [hargs] at he
        exact he
      rcases (hFree.rel_iff (.inr ()) ![e x, e x₀]).mp hRel with
        ⟨xs, _, hxs⟩ | ⟨xs, _, hxs⟩
      · exfalso
        apply hx₀
        exact ⟨xs 1, by
          have h1 := congrFun hxs (1 : Fin 2)
          simpa using h1⟩
      · exact ⟨xs 0, by
          have h0 := congrFun hxs (0 : Fin 2)
          simpa using h0⟩
    intro x
    rcases lt_trichotomy x₀ x with hlt | heq | hgt
    · exact inRight x hlt
    · subst x
      rcases hFree.covers (e x₀) with ⟨a, ha⟩ | hRight
      · exfalso
        exact hx₀ ⟨a, ha.symm⟩
      · exact hRight
    · exact inRight_rev x hgt

end AllThoseRamseyClasses.Lifts
