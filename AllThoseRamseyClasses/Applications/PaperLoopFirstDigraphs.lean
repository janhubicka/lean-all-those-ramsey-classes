import AllThoseRamseyClasses.Applications.PaperOrderedGraphs
import PartiteConstruction.Ramsey.CopywiseRamseyTransfer
import Mathlib.Order.Prod.Lex.Basic

/-!
# Admissible ordering of finite digraphs: loop vertices come first

This is the explicit example preceding the general admissible-order
proposition in the 2019 paper. A freely ordered digraph Ramsey witness
is re-ordered so that vertices with loops precede vertices without
loops, preserving the old order *within* each class.

Every FULL ordered B-copy, where B already has this loop-first
property, remains a full ordered copy after reordering. Thus the
checked B-copywise Ramsey transfer gives the actual Ramsey theorem
for loop-first ordered digraphs. No external Ramsey theorem for
unary types is assumed.
-/

namespace AllThoseRamseyClasses.Applications.PaperGraphs

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Vertex order respects the two one-vertex types:
looped vertices precede unlooped vertices. -/
def LoopFirst {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) : Prop :=
  ∀ x y : V, edge C x x → ¬ edge C y y → x < y

/-- The loop status as a two-valued order key. -/
noncomputable def loopKey {V : Type}
    (C : RelStructure Lang V) (x : V) : Fin 2 := by
  classical
  exact if edge C x x then 0 else 1

/-- Order by loop status, then by the original vertex order.
The key is injective because it also records the original vertex. -/
noncomputable def loopFirstLinearOrder {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) : LinearOrder V := by
  classical
  apply LinearOrder.lift'
    (fun x => toLex ((loopKey C x, x) : Fin 2 × V))
  intro x y h
  exact congrArg Prod.snd
    (congrArg (ofLex : Lex (Fin 2 × V) → Fin 2 × V) h)

/-- Compare vertices by their two-valued loop type first, then
by their old order within the same type. -/
theorem loopFirstLinearOrder_lt_iff {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) (x y : V) :
    (letI := loopFirstLinearOrder C; x < y) ↔
    loopKey C x < loopKey C y ∨
      (loopKey C x = loopKey C y ∧ x < y) := by
  change toLex ((loopKey C x, x) : Fin 2 × V) <
    toLex ((loopKey C y, y) : Fin 2 × V) ↔ _
  exact Prod.Lex.toLex_lt_toLex

/-- The new order has looped vertices first. -/
theorem loopFirstLinearOrder_isLoopFirst {V : Type} [LinearOrder V]
    (C : RelStructure Lang V) :
    (letI := loopFirstLinearOrder C; LoopFirst C) := by
  classical
  intro x y hx hy
  apply (loopFirstLinearOrder_lt_iff C x y).mpr
  left
  simp [loopKey, hx, hy]

/-- A full ordered embedding preserves the loop type exactly,
including the absence of loops. -/
private theorem loop_status_iff
    {U V : Type} [LinearOrder U] [LinearOrder V]
    (B : RelStructure Lang U) (C : RelStructure Lang V)
    (b : Embedding B.ordered C.ordered) (x : U) :
    edge C (b x) (b x) ↔ edge B x x := by
  have h := b.map_rel_iff (.inl .edge) ![x, x]
  have ht : (b ∘ ![x, x] : Fin 2 → V) = ![b x, b x] := by
    funext i
    fin_cases i <;> rfl
  change C.rel .edge (b ∘ ![x, x]) ↔ B.rel .edge ![x, x] at h
  rw [ht] at h
  exact h

/-- Each copy of an admissibly ordered B retains its order
after the target is sorted by one-vertex loop types. -/
private theorem loopFirst_copy_strictMono
    {U V : Type} [LinearOrder U] [LinearOrder V]
    (B : RelStructure Lang U) (C : RelStructure Lang V)
    (hB : LoopFirst B)
    (b : Embedding B.ordered C.ordered)
    (x y : U) (hxy : x < y) :
    (letI := loopFirstLinearOrder C; b x < b y) := by
  classical
  have hstatusx := loop_status_iff B C b x
  have hstatusy := loop_status_iff B C b y
  have hkey (z : U) :
      loopKey C (b z) = loopKey B z := by
    by_cases h : edge B z z
    · have ht := (loop_status_iff B C b z).mpr h
      simp [loopKey, h, ht]
    · have ht : ¬ edge C (b z) (b z) :=
        fun hh => h ((loop_status_iff B C b z).mp hh)
      simp [loopKey, h, ht]
  have hkeyLe : loopKey B x ≤ loopKey B y := by
    by_cases hx : edge B x x
    · by_cases hy : edge B y y
      · simp [loopKey, hx, hy]
      · simp [loopKey, hx, hy]
    · by_cases hy : edge B y y
      · exact False.elim (lt_asymm hxy (hB y x hy hx))
      · simp [loopKey, hx, hy]
  apply (loopFirstLinearOrder_lt_iff C (b x) (b y)).mpr
  rw [hkey x, hkey y]
  rcases lt_or_eq_of_le hkeyLe with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, b.strictMono hxy⟩

/-- Every original full B-copy survives the loop-type reordering
as a FULL ordered copy; no negative edge information is lost. -/
theorem loopFirst_preserves_ordered_copies
    {U V : Type} [LinearOrder U] [LinearOrder V]
    (B : RelStructure Lang U) (C : RelStructure Lang V)
    (hB : LoopFirst B) :
    CopywiseCompletion B.ordered C.ordered
      (@RelStructure.ordered Lang V C (loopFirstLinearOrder C).toLT)
      (fun x => x) := by
  intro b
  let e : Embedding B.ordered
      (@RelStructure.ordered Lang V C (loopFirstLinearOrder C).toLT) := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R t
      cases R with
      | inl s =>
          exact b.map_rel_iff (.inl s) t
      | inr u =>
          cases u
          let t₂ : Fin 2 → U := t
          let x : U := t₂ 0
          let y : U := t₂ 1
          change (@LT.lt V (loopFirstLinearOrder C).toLT (b x) (b y)) ↔ x < y
          constructor
          · intro hlt
            by_contra hn
            have hyx : y ≤ x := le_of_not_gt hn
            rcases eq_or_lt_of_le hyx with heq | hyxlt
            · have hh : (@LT.lt V o.toLT (b x) (b x)) := by
                simpa only [heq] using hlt
              exact (lt_irrefl _ hh)
            · have hh : (@LT.lt V (loopFirstLinearOrder C).toLT (b y) (b x)) :=
                loopFirst_copy_strictMono B C hB b y x hyxlt
              letI : LinearOrder V := loopFirstLinearOrder C
              exact (lt_asymm hlt hh).elim
          · intro hlt
            exact loopFirst_copy_strictMono B C hB b x y hlt
  }
  exact ⟨e, fun _ => rfl⟩

/-- Fully verified instance of the paper's admissible-order
reordering principle: freely ordered finite digraphs with looped
vertices before unlooped ones form a Ramsey class. -/
theorem loopFirstOrderedDigraphs_areRamsey
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure Lang U) (B : RelStructure Lang V)
    (_hA : LoopFirst A) (hB : LoopFirst B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure Lang W),
      @LoopFirst W o C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered Lang W C o.toLT) κ := by
  obtain ⟨W, hW, o, C, hRamsey⟩ :=
    freelyOrderedDigraphs_areRamsey A B κ
  letI : LinearOrder W := o
  have hCopies : CopywiseCompletion B.ordered
      (@RelStructure.ordered Lang W C o.toLT)
      (@RelStructure.ordered Lang W C
        (@loopFirstLinearOrder W o C).toLT) (fun x => x) :=
    @loopFirst_preserves_ordered_copies V W _ o B C hB
  have hArrow : StructuralRamsey.Arrow A.ordered B.ordered
      (@RelStructure.ordered Lang W C
        (@loopFirstLinearOrder W o C).toLT) κ :=
    arrow_of_BCopywiseCompletion hRamsey hCopies
  exact ⟨W, hW, @loopFirstLinearOrder W o C, C,
    @loopFirstLinearOrder_isLoopFirst W o C, hArrow⟩

end AllThoseRamseyClasses.Applications.PaperGraphs
