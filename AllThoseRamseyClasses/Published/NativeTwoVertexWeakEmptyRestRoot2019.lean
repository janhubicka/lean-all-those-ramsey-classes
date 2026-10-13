import AllThoseRamseyClasses.Published.NativeTwoRestRootCardinality2019
import AllThoseRamseyClasses.Published.NativeTwoRestClosedKRootCompletion2019
import Mathlib.Tactic

/-!
# A genuine weak TWO-vertex native two-REST source has an EMPTY closed K-root

This module strengthens the two-REST native completion programme
without silently assuming that the ORIGINAL weak source is
intrinsically U-CLOSED.

If a finite exact weak source has <=2 vertices and its genuine
native protected/ordinary projection visits the PRIVATE exteriors
of two distinct attached copy indices i,j, the literal common
root of their complementary REST source pieces omits TWO distinct
tested vertices.  Hence that common root is EMPTY.

Because every closure rule has a nonempty designated root,
the exact empty induced root is intrinsically U-CLOSED, even when
the ORIGINAL source is weak and not closed.  Ordinary
irreducibility of this empty root is vacuous.  The ORIGINAL
closed-irreducible B-copy coverage and closed heredity of K
then certify that this LITERAL root belongs to K: this also
properly handles possible nullary relational symbols, because
its full embedding into B is obtained from the actual coverage
hypothesis, not falsely fabricated by an arbitrary empty map.

The already verified two-REST completion theorem with a literal
closed K-root now completes the original two-vertex weak source
using the OLD CLOSED RANK-ONE invariant.  Source relation tuples
may cross the two HJ COPY ranges: they lie in both complementary
REST pieces as the real native free-cover lemma requires.

This is a restricted, genuinely CLOSED-ROOT native success case,
NOT a completion of arbitrary rank-two weak sources with a
nonempty core root.  It does not prove the general Lemma 2.30
or corrected Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment
open StructuralRamsey.Partite
open StructuralRamsey.Partite.Induced
open StructuralRamsey.HalesJewett

universe u v
variable {L : RelLanguage.{u}}

/-- Genuine native two-private-active exact weak source, at most
TWO original source vertices, with the original B-coverage and
old closed rank-one K-completion invariant.

The ENTIRE literal two-REST common root is automatically EMPTY,
hence intrinsically closed and irreducible, and consequently is
a K-member by actual B-coverage plus closed heredity.  No
intrinsic closedness of the original weak source is assumed. -/
theorem native2019_maximal_two_vertex_weak_two_rest_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U UB I : Type v} {N : ℕ}
    [Fintype U] [Finite V]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
    (B : RelStructure L UB)
    (hBK : K B)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test Source →
      Nonempty (Embedding Test B))
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (i j : I) (hij : i ≠ j)
    (hOnly : ∀ k : I,
      (∃ x : U, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x)) →
        k = i ∨ k = j)
    (hActiveI : ∃ x : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x))
    (hActiveJ : ∃ y : U, OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p y))
    (hCard : Fintype.card U ≤ 2)
    (hOldClosed : IsUClosed rules Old.toRelStructure)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hHer : ClosedUHereditary K rules)
    (hKIrr : ∀ {X : Type v} (S : RelStructure L X),
      K S → S.Irreducible)
    (hOldRank : ∀ (T : Set V) [Fintype T],
      IsUClosed rules (Old.toRelStructure.induce T) →
      USize rules (Old.toRelStructure.induce T) ≤ 1 →
        HasInducedClosedUKCompletion K rules
          (Old.toRelStructure.induce T)) :
    HasInducedClosedUKCompletion K rules Source := by
  classical
  let Root : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x) ∧
      ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  letI : Fintype Root := Fintype.ofFinite Root
  have hBound : Nat.card Root + 2 ≤ Fintype.card U :=
    native2019_two_rest_root_card_add_two_le_source
      (Old.support alpha) p i j hij hActiveI hActiveJ
  have hZero : Fintype.card Root = 0 := by
    have hh : Nat.card Root = 0 := by omega
    simpa only [Nat.card_eq_fintype_card] using hh
  have hNoRoot : ∀ x : Root, False := by
    intro x
    have hh : 0 < (Finset.univ : Finset Root).card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_univ x⟩
    have hPos : 0 < Fintype.card Root := by simpa using hh
    omega
  have hRootClosed : IsUClosed rules (Source.induce Root) := by
    intro rule _
    constructor
    · intro t _
      exact False.elim (hNoRoot
        (t ((⟨0, rule.rootPositive⟩ : Fin rule.rootSize).castLE
          rule.rootLE)))
    · intro e
      exact False.elim (hNoRoot (e ⟨0, rule.rootPositive⟩))
  have hRootIrred : (Source.induce Root).Irreducible :=
    native2019_two_rest_small_root_irreducible Source
      (Old.support alpha) p i j hij hActiveI hActiveJ
      (by omega : Fintype.card U ≤ 3)
  have hRootUIrred : IsUIrreducible rules (Source.induce Root) :=
    hRootIrred.isUIrreducible rules
  obtain ⟨e⟩ :=
    hCover (Source.induce Root) hRootClosed hRootUIrred
      (inclusion Source Root)
  have hRootK : K (Source.induce Root) :=
    hHer (Source.induce Root) B hBK hRootClosed e
  have hRootSet :
      Root =
      ({x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) j (p x)} ∩
       {x : U | ¬ OutsideAt
          (W := NonInduced.Vertex (Old.restrict alpha) N)
          (I := I) (Old.support alpha) i (p x)}) := by
    ext x
    rfl
  rw [hRootSet] at hRootClosed hRootK
  exact native2019_two_rest_complete_of_literal_closed_K_root
    Source hMax Old alpha A hRestricted lines p hp
    i j hij hOnly hActiveI hActiveJ
    hRootK hRootClosed 1 (by omega : Fintype.card U ≤ 1+1)
    hOldClosed hStrong hHer hKIrr hOldRank

end AllThoseRamseyClasses.Published
