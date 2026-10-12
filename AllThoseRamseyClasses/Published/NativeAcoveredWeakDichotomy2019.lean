import AllThoseRamseyClasses.Published.NativeActualWeakTrichotomy2019
import AllThoseRamseyClasses.Published.RootedWeakOneAnchor2019

/-!
# Actual 2019 Hales--Jewett weak history under an A-COVERED old Picture

The native finite-history trichotomy (PR #153) leaves an injective
ordinary Old-map alternative, which cannot be completed by the
previous unrooted weak-size W_j(Old) invariant when the exact source
has j+1 vertices and its image has j+1 distinct vertices.

Rooted weak W_j^A(Old) does more: merged PR #156 proves that a
corrected protected map of a weak j+1-vertex test is completable
if the image of just ONE source vertex lies in an embedded A-copy.
For an ordinary map from a maximal-U-rank source, protection follows.

Thus if the old Picture is additionally A-COVERED
(every Old vertex belongs to SOME full embedded A-copy), the
noncolliding injective-map alternative is automatically completed.
The true native maximal-rank trichotomy sharpens to only:

  * the ORIGINAL exact weak source has a corrected K-completion, or
  * the ORIGINAL exact weak source admits a PROPER relational free
    decomposition into sides of at most j vertices.

This is a genuine theorem from explicit hACover, hOldWeak and rooted
W_j^A premises. It neither claims that the native Ramsey Picture
automatically has A-cover nor solves transverse ROOT COMPATIBILITY.
The source is nonempty; the empty weak source has a separate trivial
completion base. No unconditional repaired Theorem 2.18 is claimed.
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

/-- Under explicit whole-Old vertex A-coverage and rooted W_j^A,
the injective-old-map branch of the ACTUAL finite native history
trichotomy disappears: one old image vertex anchors the entire
weak test's completion.

No claim that every native Old picture enjoys the A-cover premise
is made here. Two-side common boundary remains OPEN. -/
theorem native2019_Acovered_actual_active_weaksize_dichotomy
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {P Q V U I : Type v} {N : ℕ}
    [Fintype U] [Nonempty U] [Finite Q] [Finite V]
    (Source : RelStructure L U)
    (hMax : USize rules Source = Fintype.card U)
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
    (hp : Source.IsHomomorphismEmbedding
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p)
    (j : ℕ) (hCard : Fintype.card U ≤ j+1)
    (hOldWeak : ∀ T : Finset V, T.card ≤ j →
      HasInducedClosedUKCompletion K rules
        (Old.toRelStructure.induce (↑T : Set V)))
    (hRooted : Has2019RootedWeakSizeCompletions
      K rules Old.toRelStructure A j)
    (hACover : ∀ y : V,
      ∃ a : Embedding A Old.toRelStructure,
        y ∈ Set.range a) :
    HasInducedClosedUKCompletion K rules Source ∨
      (∃ d : ProperFreeDecomposition Source,
        Nat.card d.Left ≤ j ∧ Nat.card d.Right ≤ j) := by
  classical
  rcases native2019_actual_active_weaksize_trichotomy
      Source hMax Old alpha A hAK hAIrred
      hRestricted hPower lines p hp j hCard hOldWeak with
      hDone | hRest
  · exact Or.inl hDone
  rcases hRest with ⟨q, hq, _⟩ | hFree
  · let x : U := Classical.choice ‹Nonempty U›
    obtain ⟨a, hAnchor⟩ := hACover (q x)
    left
    exact inducedClosed2019_maximal_ordinary_map_one_A_anchor
      Source hMax Old.toRelStructure A
      q hq j hCard a x hAnchor hRooted
  · exact Or.inr hFree

end AllThoseRamseyClasses.Published
