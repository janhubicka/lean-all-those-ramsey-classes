import AllThoseRamseyClasses.Published.NativeProtectedZeroActive2019

/-!
# The exact intersection of TWO native REST source pieces has a K-completion

Let an original EXACT weak source F carry a corrected protected
homomorphism-embedding p into the genuine simultaneous Hales--Jewett
attachment. Assume the only private-active attached-copy indices of
F are i and j, where i ≠ j.

The exact overlap of complementary REST source pieces is

  H = {x : F | p(x) is neither private exterior i nor private exterior j}.

Because the only source-active indices are i,j, EVERY ORIGINAL
vertex of H projects into the genuine N-fold POWER CORE: no projected
private exterior of ANY index occurs. Restricting a corrected
protected source map to the literal induced H preserves protection.

The already-verified arbitrary-rank zero-active native completion
theorem then sends H protectedly through the genuine native core's
part map into the specified closed irreducible A∈K, giving a
corrected (K,U)-completion of the WHOLE ORIGINAL root H.

Neither F nor H is required intrinsically closed, finite, or
maximal rank. No global injectivity or target semi-closedness is used.

WARNING: the conclusion is a PROTECTED completion map H→A, not
necessarily an INDUCED EMBEDDING H↪A. To glue independent K
completions of the two REST sides via strong amalgamation one
needs FULL embeddings of a common CLOSED K-boundary, and the two
ordinary old REST maps must factor compatibly through that
boundary. This theorem does NOT provide those strong conditions.
It isolates the exact remaining two-active-line obstruction.

The unrestricted 2019 Lemma 2.30 and corrected Theorem 2.18
remain OPEN.
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

/-- The ORIGINAL exact common REST-root is completable in A, under
a protected map to genuine native attachment with source-private-active
copy indices contained in {i,j}. No intrinsic size/rank hypothesis.

This does NOT claim both ordinary old REST side maps factor through
full A embeddings on that root: protected q:H→A may be noninjective. -/
theorem native2019_two_only_active_rest_root_has_A_completion
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Finite Q]
    (Source : RelStructure L U)
    (Old : System L P V)
    (alpha : Q ↪ P) (A : RelStructure L Q)
    (hAK : K A) (hAIrred : A.Irreducible)
    (hRestricted : (Old.restrict alpha).IsPartiteOver A)
    (hPower : IsClosedUHomomorphismEmbedding rules
      (power (Old.restrict alpha) N).toRelStructure A
      (power (Old.restrict alpha) N).part)
    (lines : I → Line (Letter A (Old.restrict alpha)) N)
    (p : U → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I))
    (hp : IsInducedClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (i j : I) (hij : i ≠ j)
    (hOnly : ∀ k : I,
      (∃ x : U, OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (p x)) →
        k = i ∨ k = j) :
    let Root : Set U :=
      {x | ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) j (p x) ∧
           ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (p x)}
    HasInducedClosedUKCompletion K rules (Source.induce Root) := by
  classical
  let Root : Set U :=
    {x | ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) j (p x) ∧
         ¬ OutsideAt
      (W := NonInduced.Vertex (Old.restrict alpha) N)
      (I := I) (Old.support alpha) i (p x)}
  let pRoot : Root → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I) :=
    fun x => p x.1
  have hpAbs : IsClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hpRoot : IsInducedClosedUHomomorphismEmbedding rules
      (Source.induce Root)
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) pRoot :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (hpAbs.precomp_embedding (inclusion Source Root))
  have hNoPrivate : ∀ x : Root, ∀ k : I,
      ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) k (pRoot x) := by
    intro x k hOutside
    rcases hOnly k ⟨x.1, hOutside⟩ with hi | hj
    · subst k
      exact x.2.2 hOutside
    · subst k
      exact x.2.1 hOutside
  exact native2019_protected_zero_active_has_A_completion
    (Source.induce Root) Old alpha A hAK hAIrred
    hRestricted hPower lines pRoot hpRoot hNoPrivate

end AllThoseRamseyClasses.Published
