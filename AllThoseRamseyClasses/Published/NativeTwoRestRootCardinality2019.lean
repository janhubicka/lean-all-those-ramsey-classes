import AllThoseRamseyClasses.Published.NativeTwoRestFree2019
import Mathlib.Tactic

/-!
# Genuine two-REST source: the literal core root misses TWO source vertices

For any original finite source mapping to the TRUE native attachment,
two distinct private-active copy indices i≠j yield TWO different
original source vertices outside the literal common REST root:
one private exterior of i and one of j. The two-REST source geometry
already proves properness of each rest side (merged PR #176).

This file sharpens the absolute cardinality arithmetic: the induced
source root has at least TWO fewer actual source vertices,

   |literal REST_i ∩ REST_j source root| + 2 <= |Source|.

The proof factors the cardinal inequality through two successive
genuine proper inclusions Root⊊REST_j⊊Source. No closure hulls,
embedding of the noninjective native projection, or U-generating
rank hypotheses are used.

In particular if |Source|<=3, the exact induced root has at most
ONE vertex and is ORDINARY irreducible. The condition is genuinely
about the SOURCE vertex set, not the rank or size of projected
closed hulls.

For a source that is itself U-CLOSED and has maximal generating
rank, this may combine with the original B-coverage lemma for
irreducible closed roots; it does NOT say arbitrary weak roots
are U-closed or K-members, nor prove general Lemma 2.30.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- With two distinct source-private-active native copy labels,
the LITERAL common REST source root misses at least TWO original
source vertices. No source-map positivity or injectivity is used:
only the unique exterior label of an actual attachment vertex. -/
theorem native2019_two_rest_root_card_add_two_le_source
    {U V W I : Type v} [Fintype U]
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I))
    (i j : I) (hij : i ≠ j)
    (hActiveI : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U,
      OutsideAt (W := W) (I := I) Support j (p y)) :
    let Root : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support j (p x) ∧
            ¬ OutsideAt (W := W) (I := I) Support i (p x)}
    Nat.card Root + 2 ≤ Fintype.card U := by
  classical
  let Left : Set U := {x | ¬ OutsideAt
    (W := W) (I := I) Support j (p x)}
  let Root : Set U := {x | x ∈ Left ∧ ¬ OutsideAt
    (W := W) (I := I) Support i (p x)}
  letI : Fintype Left := Fintype.ofFinite Left
  letI : Fintype Root := Fintype.ofFinite Root
  let e : Root → Left := fun x => ⟨x.1, x.2.1⟩
  have he : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Left => z.1) hxy
  have heNotSurj : ¬ Function.Surjective e := by
    intro hSurj
    obtain ⟨x, hx⟩ := hActiveI
    have hxLeft : x ∈ Left := by
      intro hj
      exact hij (native2019_private_exterior_index_unique
        Support hx hj)
    obtain ⟨z, hz⟩ := hSurj ⟨x, hxLeft⟩
    have hzVal : z.1 = x :=
      congrArg (fun w : Left => w.1) hz
    have hzRoot : x ∈ Root := hzVal ▸ z.2
    exact hzRoot.2 hx
  have hRootSmall : Fintype.card Root < Fintype.card Left :=
    Fintype.card_lt_of_injective_not_surjective e he heNotSurj
  let inc : Left → U := Subtype.val
  have hInc : Function.Injective inc := Subtype.val_injective
  have hIncNotSurj : ¬ Function.Surjective inc := by
    intro hSurj
    obtain ⟨y, hy⟩ := hActiveJ
    obtain ⟨z, hz⟩ := hSurj y
    have hzVal : z.1 = y := hz
    exact (hzVal ▸ z.2) hy
  have hLeftSmall : Fintype.card Left < Fintype.card U :=
    Fintype.card_lt_of_injective_not_surjective inc hInc hIncNotSurj
  have hBound : Fintype.card Root + 2 ≤ Fintype.card U := by omega
  simpa only [Nat.card_eq_fintype_card] using hBound

/-- If the original exact source has at most THREE vertices and
visits private exteriors of two DIFFERENT attachment indices,
the entire common REST root contains at most one source vertex.

This is an absolute cardinal bound, not a closed projected rank bound. -/
theorem native2019_two_rest_root_card_le_one_of_source_le_three
    {U V W I : Type v} [Fintype U]
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I))
    (i j : I) (hij : i ≠ j)
    (hActiveI : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U,
      OutsideAt (W := W) (I := I) Support j (p y))
    (hCard : Fintype.card U ≤ 3) :
    let Root : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support j (p x) ∧
            ¬ OutsideAt (W := W) (I := I) Support i (p x)}
    Nat.card Root ≤ 1 := by
  have h := native2019_two_rest_root_card_add_two_le_source
    Support p i j hij hActiveI hActiveJ
  omega

/-- The root of the TWO genuine RESTS of a ≤3-vertex test
is ORDINARY irreducible, because its exact source carrier
has cardinal at most one. It is not automatically U-CLOSED. -/
theorem native2019_two_rest_small_root_irreducible
    {U V W I : Type v} [Fintype U]
    (Source : RelStructure L U)
    (Support : Set V)
    (p : U → Vertex Support (W := W) (I := I))
    (i j : I) (hij : i ≠ j)
    (hActiveI : ∃ x : U,
      OutsideAt (W := W) (I := I) Support i (p x))
    (hActiveJ : ∃ y : U,
      OutsideAt (W := W) (I := I) Support j (p y))
    (hCard : Fintype.card U ≤ 3) :
    let Root : Set U :=
      {x | ¬ OutsideAt (W := W) (I := I) Support j (p x) ∧
            ¬ OutsideAt (W := W) (I := I) Support i (p x)}
    (Source.induce Root).Irreducible := by
  classical
  let Root : Set U :=
    {x | ¬ OutsideAt (W := W) (I := I) Support j (p x) ∧
          ¬ OutsideAt (W := W) (I := I) Support i (p x)}
  letI : Fintype Root := Fintype.ofFinite Root
  have hRootCardNat : Nat.card Root ≤ 1 :=
    native2019_two_rest_root_card_le_one_of_source_le_three
      Support p i j hij hActiveI hActiveJ hCard
  have hRootCard : Fintype.card Root ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card] using hRootCardNat
  intro x y hxy
  have hFin : (Finset.univ : Finset Root).card ≤ 1 := by
    simpa using hRootCard
  have heq : x = y :=
    Finset.card_le_one.mp hFin x (Finset.mem_univ x)
      y (Finset.mem_univ y)
  exact (hxy heq).elim

end AllThoseRamseyClasses.Published
