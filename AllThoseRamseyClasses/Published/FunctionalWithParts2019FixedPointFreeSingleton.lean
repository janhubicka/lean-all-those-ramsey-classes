import AllThoseRamseyClasses.Published.FunctionalWithParts2019IntrinsicSingletonVacuity
import PartiteConstruction.Structure.PartialSetFunctionsClosed

/-!
# Track C: nontrivial finite functional class with vacuous full-weak local axiom

A genuine partial unary function with a NONEMPTY singleton value
distinct from the argument has no induced one-vertex full substructure:
on an intrinsically weak singleton the operation can only be
undefined, defined-empty, or have its output equal to that singleton.
A full embedding must reflect its exact Option(Set) value. Consequently
NO intrinsically weak singleton of ANY source can fully embed into
this class.

This class is nonempty (the two-vertex swap is a member) and is
hereditary under genuine function-closed restrictions, the correct
2019 notion. By the general singleton-vacuity lemma its proposed
full-intrinsic-weak local-completion axiom holds at cutoff one,
regardless of the control structure.

This by itself does NOT establish that this class is non-Ramsey,
strong-amalgamation, or a counterexample to the COMPLETE 2019
class theorem. It shows exactly why a local axiom using full
intrinsic weak tests is too easy to satisfy in natural functional
classes, whereas the ambient-relative repaired axiom is not.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.PartialSetStructure

/-- Finite source structures whose genuine unary function is
everywhere defined with a single output DISTINCT from its input. -/
def fixedPointFreeUnaryPartiteH :
    GenuinePartite2019Class
      (L := exampleLanguage) (Parts := Fin 2) :=
  fun {X} (A : PartialSetStructure exampleLanguage X) _ =>
    ∀ x : X, ∃ y : X,
      y ≠ x ∧ A.func () (fun _ : Fin 1 => x) = some ({y} : Set X)

/-- An explicit nonempty example: a two-point fixed-point-free swap.
Part labels are arbitrary here and have no effect on the function. -/
private def fixedPointFreeSwap :
    PartialSetStructure exampleLanguage (Fin 2) where
  rel := fun R => Empty.elim R
  func := fun _ xs =>
    if xs (0 : Fin 1) = (0 : Fin 2)
    then some ({(1 : Fin 2)} : Set (Fin 2))
    else some ({(0 : Fin 2)} : Set (Fin 2))

theorem fixedPointFreeUnaryPartiteH_nonempty :
    ∃ (X : Type) (_ : Finite X)
      (A : PartialSetStructure exampleLanguage X)
      (part : X → Fin 2),
      fixedPointFreeUnaryPartiteH A part := by
  refine ⟨Fin 2, inferInstance, fixedPointFreeSwap,
    (fun x : Fin 2 => x), ?_⟩
  intro x
  fin_cases x
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨0, by decide, rfl⟩

/-- The fixed-point-free unary condition is preserved by every
genuinely FUNCTION-CLOSED restriction. The successor of each chosen
vertex remains inside the closed carrier, and the same singleton
function value survives with its defined domain bit. -/
theorem fixedPointFreeUnaryPartiteH_closedHereditary :
    GenuinePartiteClosedHereditary2019
      fixedPointFreeUnaryPartiteH := by
  intro X hFinite A part hMem S hClosed z
  obtain ⟨y, hy, hVal⟩ := hMem z.1
  have hyS : y ∈ S :=
    hClosed () (fun _ : Fin 1 => z.1) ({y} : Set X)
      (fun _ => z.2) hVal (by simp)
  let yS : S := ⟨y, hyS⟩
  refine ⟨yS, ?_, ?_⟩
  · intro hEq
    exact hy (congrArg Subtype.val hEq)
  · change (A.func () (fun _ : Fin 1 => z.1)).map
        (fun T => {u : S | u.1 ∈ T}) =
        some ({yS} : Set S)
    rw [hVal]
    change some ({u : S | u.1 ∈ ({y} : Set X)}) =
      some ({yS} : Set S)
    congr 1
    ext u
    constructor
    · intro hu
      apply Subtype.ext
      exact Set.mem_singleton_iff.mp hu
    · intro hu
      have heq : u = yS := Set.mem_singleton_iff.mp hu
      change u.1 ∈ ({y} : Set X)
      rw [heq]
      simp [yS]

/-- NO full genuinely partial-function embedding of ANY whole-weak
singleton into a fixed-point-free unary H-member exists, even if the
source is an arbitrary partial structure. The proof explicitly
checks the none/some cases and does not identify defined-empty
with undefined. -/
theorem fixedPointFreeUnaryPartiteH_noWeakSingleton :
    NoIntrinsicFullWeakSingletonHCompletions
      fixedPointFreeUnaryPartiteH := by
  intro V hFinite A x
  rintro ⟨X, hX, Target, partTarget, hH, ⟨e⟩⟩
  let S : Set V := {x}
  let xs : Fin 1 → S := fun _ => ⟨x, Set.mem_singleton x⟩
  obtain ⟨y, hy, hY⟩ := hH (e.toFun (xs 0))
  have hInput : (e.toFun ∘ xs) =
      (fun _ : Fin 1 => e.toFun (xs 0)) := by
    funext i
    fin_cases i
    rfl
  have hTarget : Target.func () (e.toFun ∘ xs) =
      some ({y} : Set X) := by
    rw [hInput]
    exact hY
  have hMap := e.map_func () xs
  rw [hTarget] at hMap
  cases hSource : (wholeWeakInduce A S).func () xs with
  | none =>
      rw [hSource] at hMap
      cases hMap
  | some U =>
      rw [hSource] at hMap
      have hSet : Structure.imageSet e.toFun U = ({y} : Set X) :=
        Option.some.inj (by simpa only [Option.map_some] using hMap)
      have hyMem : y ∈ Structure.imageSet e.toFun U := by
        rw [hSet]
        simp
      obtain ⟨z, hz, hEq⟩ := hyMem
      have hOnly : z = xs 0 := by
        apply Subtype.ext
        exact (Set.mem_singleton_iff.mp z.2).trans
          (Set.mem_singleton_iff.mp (xs 0).2).symm
      have hySame : y = e.toFun (xs 0) :=
        hEq.symm.trans (congrArg e.toFun hOnly)
      exact hy hySame

/-- Already at cutoff n=1, the full-intrinsic-weak proposed local
class axiom becomes automatic for this nonempty class, for every
canonical member B and every possible control C0. This is a
precise logical vacuity result, not a global Ramsey assertion. -/
theorem fixedPointFreeUnary_fullWeakLocalAtOne
    {W Z : Type}
    (B : RelStructure
      ((exampleLanguage.withParts (Fin 2)).wholeMaskTagLanguage (Fin 2)) W)
    (hB : canonicalGenuineTagged2019Class fixedPointFreeUnaryPartiteH B)
    (C0 : RelStructure
      ((exampleLanguage.withParts (Fin 2)).wholeMaskTagLanguage (Fin 2)) Z) :
    GenuinePartiteIntrinsicFullWeakLocalCompletionAt
      fixedPointFreeUnaryPartiteH B C0 1 :=
  intrinsicFullWeakLocalCompletionAt_one_of_noSingletons
    fixedPointFreeUnaryPartiteH
    fixedPointFreeUnaryPartiteH_noWeakSingleton
    B hB C0

end AllThoseRamseyClasses.Published
