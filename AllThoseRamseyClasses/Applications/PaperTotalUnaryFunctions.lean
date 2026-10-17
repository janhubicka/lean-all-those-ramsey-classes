import AllThoseRamseyClasses.Applications.FunctionFibreUtilities
import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import Mathlib.Tactic

/-!
# The finite-target case of paper Theorem thm:unaryfunc

Every structure has a FIXED finite family of total single-valued unary
operations, indexed by Fin m, together with an arbitrary free vertex
order. The upstream set-valued functional language represents each
genuine operation by an exactly singleton-valued fibre. We prove
this representation equivalent to an actual family of total functions.

The class is hereditary under FULL functional embeddings: the unique
output in the target has a unique source preimage. It is preserved by
FULL strong free amalgamation because unary inputs (and their unique
outputs) live entirely on one side. The general checked functional
free-amalgamation Ramsey theorem now gives a finite ordered target.

This is intentionally NOT the countably infinite-B extension of
Theorem thm:unaryfunc, nor its additional countability assertion.
-/

namespace AllThoseRamseyClasses.Applications.TotalUnaryFunctions

open StructuralRamsey
open StructuralRamsey.Structure

/-- Exactly m unary function symbols, and no relation symbols. -/
abbrev Lang (m : ℕ) : Language where
  RelSymbol := PEmpty
  FuncSymbol := Fin m
  relArity := PEmpty.elim
  funcArity := fun _ => 1

def outputs (m : ℕ) {V : Type}
    (C : Structure (Lang m) V) (i : Fin m) (x : V) : Set V :=
  C.func i ![x]

/-- The total unary class in the upstream set-valued functional language.
Every input's output set contains exactly one vertex. -/
def totalUnaryClass (m : ℕ) : StructureClass (L := Lang m) :=
  fun {V} (C : Structure (Lang m) V) =>
    Finite V ∧ ∀ (i : Fin m) (x : V),
      ∃ y : V, outputs m C i x = {y}

/-- Precisely the class of genuine total unary-function algebras. -/
theorem totalUnaryClass_iff_functions
    (m : ℕ) {V : Type} (C : Structure (Lang m) V) :
    totalUnaryClass m C ↔
      Finite V ∧ ∃ f : Fin m → V → V,
        ∀ (i : Fin m) (x : V), outputs m C i x = {f i x} := by
  classical
  constructor
  · intro h
    choose f hf using h.2
    exact ⟨h.1, f, hf⟩
  · rintro ⟨hFinite, f, hf⟩
    exact ⟨hFinite, fun i x => ⟨f i x, hf i x⟩⟩

/-- Full functional embeddings map the WHOLE fibre bijectively onto the
target fibre, not merely a positively named graph edge. -/
theorem outputs_image
    (m : ℕ) {U V : Type}
    {A : Structure (Lang m) U} {B : Structure (Lang m) V}
    (e : Embedding A B) (i : Fin m) (x : U) :
    e '' outputs m A i x = outputs m B i (e x) := by
  change imageSet e (A.func i ![x]) = B.func i ![e x]
  have ht : e ∘ ![x] = ![e x] := by
    funext j
    fin_cases j <;> rfl
  rw [← ht]
  exact e.map_func i ![x]

/-- Uniqueness of a target output, together with FULL functional
embedding, forces a unique source output. -/
theorem singleton_output_pullback
    (m : ℕ) {U V : Type}
    {A : Structure (Lang m) U} {B : Structure (Lang m) V}
    (e : Embedding A B) (i : Fin m) (x : U) (b : V)
    (hB : outputs m B i (e x) = {b}) :
    ∃ a : U, outputs m A i x = {a} ∧ e a = b := by
  exact FunctionFibreUtilities.singleton_pullback_of_image
    e e.injective (outputs_image m e i x) b hB

/-- Embedded singleton values remain singleton values in the target. -/
theorem outputs_singleton_map
    (m : ℕ) {U V : Type}
    {A : Structure (Lang m) U} {B : Structure (Lang m) V}
    (e : Embedding A B) (i : Fin m) (x y : U)
    (h : outputs m A i x = {y}) :
    outputs m B i (e x) = {e y} := by
  exact FunctionFibreUtilities.singleton_map_of_image
    e (outputs_image m e i x) y h

/-- The class of all finite m-unary algebras really has FULL functional
free amalgamation over full function-closed embeddings. -/
theorem totalUnaryClass_freeAmalgamation (m : ℕ) :
    FreeAmalgamationClass (totalUnaryClass m) := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    exact totalUnaryClass_hereditary m hB e
  · intro H E F P D A B C sA sB iA iB hA hB hFree
    have hP : Finite P := by
      letI : Finite E := hA.1
      letI : Finite F := hB.1
      exact FunctionFibreUtilities.finite_of_two_image_cover
        iA iB hFree.covers
    refine ⟨hP, ?_⟩
    intro i x
    rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · obtain ⟨y, hAy⟩ := hA.2 i a
      refine ⟨iA y, ?_⟩
      simpa [ha] using outputs_singleton_map m iA i a y hAy
    · obtain ⟨y, hBy⟩ := hB.2 i b
      refine ⟨iB y, ?_⟩
      simpa [hb] using outputs_singleton_map m iB i b y hBy

/-- Finite-target part of the actual manuscript Theorem thm:unaryfunc,
for all m and every finite nonempty colour type. In particular it
gives the requested two-colour arrow, with a finite Ramsey target. -/
theorem freelyOrderedTotalUnaryFunctions_areRamsey
    (m : ℕ) {U V : Type}
    [Finite U] [Finite V] [LinearOrder U] [LinearOrder V]
    (A : Structure (Lang m) U) (B : Structure (Lang m) V)
    (hA : totalUnaryClass m A) (hB : totalUnaryClass m B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : Structure (Lang m) W),
      totalUnaryClass m C ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder (Lang m) W C o.toLT) κ := by
  have hPositive : (Lang m).PositiveFuncArity := by
    intro F
    change (0 : ℕ) < 1
    exact Nat.zero_lt_one
  exact FreeAmalgamationClass.orderedRamsey
    (totalUnaryClass_freeAmalgamation m) A B hA hB hPositive κ

end AllThoseRamseyClasses.Applications.TotalUnaryFunctions
