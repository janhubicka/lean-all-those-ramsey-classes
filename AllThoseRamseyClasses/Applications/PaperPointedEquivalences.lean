import PartiteConstruction.Ramsey.FreeAmalgamationFunctions
import Mathlib.Tactic

/-!
# Paper example thm:pointed: freely ordered pointed equivalence relations

The total idempotent unary map x ↦ f(x) selects exactly one distinguished
vertex from each equivalence class.  The upstream EHN language interprets
functions by sets of outputs. We make those sets SINGLETONS, and explicitly
prove equivalence with a genuine total idempotent unary function.

Full functional embeddings reflect the entire singleton fibre, not merely
the positive binary graph of the function. Free amalgamations of such
pointed structures are again pointed structures, because each input
vertex and its chosen point lie within the same side. Consequently the
checked functional free-amalgamation Ramsey theorem applies with no
conditional class hypothesis.

The added linear vertex order is FREE, not required to be convex.
-/

namespace AllThoseRamseyClasses.Applications.PointedEquivalences

open StructuralRamsey
open StructuralRamsey.Structure

/-- One unary selection function and no relation symbols. -/
abbrev Lang : Language where
  RelSymbol := PEmpty
  FuncSymbol := Unit
  relArity := PEmpty.elim
  funcArity := fun _ => 1

def outputs {V : Type} (C : Structure Lang V) (x : V) : Set V :=
  C.func () ![x]

/-- Finite pointed equivalences in their exact total unary presentation:
each singleton output y is itself a fixed point. -/
def pointedClass : StructureClass (L := Lang) :=
  fun {V} (C : Structure Lang V) =>
    Finite V ∧ ∀ x : V,
      ∃ y : V, outputs C x = {y} ∧ outputs C y = {y}

/-- The set-valued encoding says exactly that a total idempotent unary
function is present, without loss of finite-algebra information. -/
theorem pointedClass_iff_total_idempotent
    {V : Type} (C : Structure Lang V) :
    pointedClass C ↔
      Finite V ∧
      ∃ f : V → V, (∀ x, outputs C x = {f x}) ∧
        (∀ x, f (f x) = f x) := by
  classical
  constructor
  · intro h
    choose f hf using h.2
    refine ⟨h.1, f, (fun x => (hf x).1), ?_⟩
    intro x
    have hEq : ({f (f x)} : Set V) = {f x} :=
      ((hf (f x)).1).symm.trans (hf x).2
    exact Set.singleton_eq_singleton_iff.mp hEq
  · rintro ⟨hFinite, f, hFunc, hIdem⟩
    refine ⟨hFinite, ?_⟩
    intro x
    refine ⟨f x, hFunc x, ?_⟩
    simpa only [hIdem x] using hFunc (f x)

/-- A full functional embedding transports the entire singleton-valued
fibre, including its unique distinguished point. -/
theorem outputs_image
    {U V : Type} {A : Structure Lang U} {B : Structure Lang V}
    (e : Embedding A B) (x : U) :
    e '' outputs A x = outputs B (e x) := by
  change imageSet e (A.func () ![x]) = B.func () ![e x]
  have ht : e ∘ ![x] = ![e x] := by
    funext i
    fin_cases i <;> rfl
  rw [← ht]
  exact e.map_func () ![x]

/-- An abstract unique point of an embedded functional fibre must have
a preimage, and that preimage is uniquely selected in the source. -/
theorem singleton_output_pullback
    {U V : Type} {A : Structure Lang U} {B : Structure Lang V}
    (e : Embedding A B) (x : U) (b : V)
    (hB : outputs B (e x) = {b}) :
    ∃ a : U, outputs A x = {a} ∧ e a = b := by
  have hb : b ∈ outputs B (e x) := by
    rw [hB]
    exact Set.mem_singleton_iff.mpr rfl
  rw [← outputs_image e x] at hb
  obtain ⟨a, ha, hea⟩ := hb
  refine ⟨a, ?_, hea⟩
  ext z
  constructor
  · intro hz
    have hez : e z ∈ outputs B (e x) := by
      rw [← outputs_image e x]
      exact ⟨z, hz, rfl⟩
    rw [hB] at hez
    have hza : z = a :=
      e.injective ((Set.mem_singleton_iff.mp hez).trans hea.symm)
    exact Set.mem_singleton_iff.mpr hza
  · intro hz
    have hza : z = a := Set.mem_singleton_iff.mp hz
    subst z
    exact ha

/-- A singleton functional fibre stays singleton under an embedding. -/
theorem outputs_singleton_map
    {U V : Type} {A : Structure Lang U} {B : Structure Lang V}
    (e : Embedding A B) (x y : U)
    (h : outputs A x = {y}) :
    outputs B (e x) = {e y} := by
  calc
    outputs B (e x) = e '' outputs A x := (outputs_image e x).symm
    _ = e '' {y} := by rw [h]
    _ = {e y} := by simp

/-- Pullback along any full embedding keeps totality and idempotency;
ordinary induced relational subsets would not suffice. -/
theorem pointedClass_hereditary
    {U V : Type} {A : Structure Lang U} {B : Structure Lang V}
    (hB : pointedClass B) (e : Embedding A B) :
    pointedClass A := by
  letI : Finite V := hB.1
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  intro x
  obtain ⟨b, hBx, hBb⟩ := hB.2 (e x)
  obtain ⟨a, hAx, hea⟩ := singleton_output_pullback e x b hBx
  have hBaa : outputs B (e a) = {e a} := by
    simpa [hea] using hBb
  obtain ⟨z, hAaz, hez⟩ := singleton_output_pullback e a (e a) hBaa
  have hza : z = a := e.injective hez
  refine ⟨a, hAx, ?_⟩
  simpa only [hza] using hAaz

/-- A genuine free amalgam does not create new values of a unary
function over old vertices; full side embeddings already say so. -/
theorem pointedClass_freeAmalgamation :
    FreeAmalgamationClass pointedClass := by
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    exact pointedClass_hereditary hB e
  · intro H E F P D A B C sA sB iA iB hA hB hFree
    have hP : Finite P := by
      letI : Finite E := hA.1
      letI : Finite F := hB.1
      apply Finite.of_surjective
        (fun z : E ⊕ F => Sum.elim iA iB z)
      intro z
      rcases hFree.covers z with ⟨a, ha⟩ | ⟨b, hb⟩
      · exact ⟨Sum.inl a, ha.symm⟩
      · exact ⟨Sum.inr b, hb.symm⟩
    refine ⟨hP, ?_⟩
    intro x
    rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · obtain ⟨y, hAy, hAyy⟩ := hA.2 a
      refine ⟨iA y, ?_, outputs_singleton_map iA y y hAyy⟩
      simpa [ha] using outputs_singleton_map iA a y hAy
    · obtain ⟨y, hBy, hByy⟩ := hB.2 b
      refine ⟨iB y, ?_, outputs_singleton_map iB y y hByy⟩
      simpa [hb] using outputs_singleton_map iB b y hBy

/-- Exact finite form of paper theorem thm:pointed. The Ramsey arrows
colour FULL order-preserving pointed-equivalence embeddings. -/
theorem freelyOrderedPointedEquivalences_areRamsey
    {U V : Type} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : Structure Lang U) (B : Structure Lang V)
    (hA : pointedClass A) (hB : pointedClass B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : Structure Lang W),
      pointedClass C ∧
      Arrow A.withLinearOrder B.withLinearOrder
        (@Structure.withLinearOrder Lang W C o.toLT) κ := by
  have hPositive : Lang.PositiveFuncArity := by
    intro F
    cases F
    decide
  exact FreeAmalgamationClass.orderedRamsey
    pointedClass_freeAmalgamation A B hA hB hPositive κ

end AllThoseRamseyClasses.Applications.PointedEquivalences
