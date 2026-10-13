import AllThoseRamseyClasses.Published.NativeTransverseCoreCrossing2019

/-!
# Two native REST roots can fail fixed-A letter compatibility

The true complementary two-REST source cover retains the ENTIRE tested
coordinate-power core in both sides. Even when each REST separately
folds ordinarily into Old along its own parameter coordinate, the
ROOT need not be contained in a single embedded copy of the fixed A.

We isolate the simplest algebraic obstruction, using the same
two-coordinate Boolean reflexive-order core as the independently
CI-green native crossing regression PR #170:

  z=(false,false), w=(true,true).

Both are central core vertices, hence belong to both complementary
REST sets of any two distinct native attached copy indices. Evaluating
either coordinate sends z to false and w to true. For the chosen
control A=PUnit (one point), there is NO pair of functions
a:A→Bool and q:{z,w}→A for which BOTH old values are recovered
as a(q(z)) and a(q(w)): the image of any A→Bool has one point.

This is deliberately only a small EVALUATION-LEVEL negative result,
not a statement about universal K-amalgamation or a formal instance
of every original closure condition. It refutes the invalid shortcut
"common REST root lies in one fixed embedded A-letter word" and
clarifies the remaining need for a potentially LARGER compatible
closed K-boundary in the genuine native Lemma 2.30.

The corrected Ramsey theorem is not contradicted.
-/

namespace AllThoseRamseyClasses.Published

/-- Two coordinate core vertices carry two distinct old evaluation
values. They cannot both factor through ONE PUnit-root letter,
even if the root parameter q is allowed to be noninjective.

This prevents confusing a protected map to the *singleton* control
A with FULL embeddings of the entire REST root into A. -/
theorem native2019_two_core_values_do_not_factor_one_singleton_letter :
    ¬ ∃ (a : PUnit → Bool) (q : Bool → PUnit),
       ∀ b : Bool, b = a (q b) := by
  rintro ⟨a, q, h⟩
  have hf := h false
  have ht := h true
  have heq : q false = q true := Subsingleton.elim _ _
  have hb : (false : Bool) = true := by
    calc
      false = a (q false) := hf
      _ = a (q true) := congrArg a heq
      _ = true := ht.symm
  cases hb

/-- In the same two-coordinate core, both coordinate evaluations of
the two displayed root vertices are respectively false and true.
Thus the previous obstruction applies to either ordinary selected
coordinate REST fold. -/
theorem native2019_two_core_points_have_distinct_selected_evaluations :
    (false, false).1 = false ∧
    (true, true).1 = true ∧
    (false, false).2 = false ∧
    (true, true).2 = true := by
  decide

end AllThoseRamseyClasses.Published
