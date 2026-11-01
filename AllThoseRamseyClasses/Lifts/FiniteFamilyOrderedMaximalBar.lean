import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalBarWitness
import AllThoseRamseyClasses.Lifts.FiniteWitnessOrderExtension

/-!
# Track E: a canonical ORDERED enlarged marked maximizing witness

The unordered finite-family maximal induced-trace age has a genuine
finite marked enlargement Bbar of every member B, with literal
old functional shadow W_B equal to a finite maximizing witness
of B. The actual full native root embedding iW : shadow(B) -> W_B
is the vertex map of the full expanded marked B-copy.

There is no reason for the native witness W_B to come with an
order compatible with the prescribed external order on B.
The independently verified finite order-extension lemma selects
a total order on W_B making the injection iW strictly monotone.
The marked B -> Bbar embedding then extends to a FULL ORDERED
embedding, while still preserving the complete old function
fibres and both truth values of every added component predicate.

Thus the enlarged Bbar used as the right Ramsey pattern can
itself be an actual member of the hereditary maximal-trace age
and carry a compatible external linear order. This construction
does not assume JEP, Ramsey, free amalgamation of mixed added
predicates, or any local weak-test sparsening theorem.

The original Section 3 regular infinite-family distinct-root
lifting theorem remains separate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every ordered finite-family maximal induced trace B has an
actual finite age-member enlargement Bbar, a finite native
forbidden-free maximizing witness W, and a CHOSEN total order
on the common W/Bbar carrier extending B's prescribed order.

The marked embedding is FULL in the ordered expanded language,
and its underlying map is exactly the native full embedding
of shadow(B) into W. Neither the completion nor any order is
postulated without construction. -/
theorem finiteNamedMaximalTraceAge_exists_orderedMarkedBar
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB : Type} [LinearOrder VB]
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (hB : IsFiniteNamedMaximalTrace Family B) :
    ∃ (VW : Type)
      (W : Structure L VW)
      (Bbar : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VW)
      (o : LinearOrder VW),
      Finite VW ∧
      AvoidsFiniteNamedEHN Family W ∧
      IsFiniteNamedMaximalTrace Family Bbar ∧
      FiniteNamedTraceShadow Family Bbar = W ∧
      ∃ (iW : Structure.Embedding
        (FiniteNamedTraceShadow Family B) W)
        (mark : Structure.Embedding B.withLinearOrder
          (@Structure.withLinearOrder _ VW Bbar o.toLT)),
        ∀ x : VB, mark x = iW x := by
  classical
  obtain ⟨VW, W, hFinW, hAvoidW, iW,
    Bbar, hBar, hShadow, mark, hmark⟩ :=
    finiteNamedMaximalTraceAge_exists_markedBar Family B hB
  letI : Finite VW := hFinW
  obtain ⟨o, hOrder⟩ :=
    exists_finiteLinearOrder_extending_injection iW iW.injective
  letI : LinearOrder VW := o
  have hMarkStrict : StrictMono mark := by
    intro x y hxy
    rw [hmark x, hmark y]
    exact hOrder x y hxy
  let markOrdered : Structure.Embedding B.withLinearOrder
      (@Structure.withLinearOrder _ VW Bbar o.toLT) := {
    toFun := mark
    injective := mark.injective
    map_rel_iff := by
      intro R xs
      cases R with
      | inl R => exact mark.map_rel_iff R xs
      | inr _ => exact hMarkStrict.lt_iff_lt
    map_func := mark.map_func
  }
  exact ⟨VW, W, Bbar, o, hFinW, hAvoidW,
    hBar, hShadow, iW, markOrdered, hmark⟩

end AllThoseRamseyClasses.Lifts
