import AllThoseRamseyClasses.Published.NativeProtectedZeroActive2019
import AllThoseRamseyClasses.Published.NativeFiniteActiveHistory2019

/-!
# Every EXACT weak test with zero private-active HJ lines completes in A

The entire paper-faithful corrected 2019 Picture C carries a protected
positive map to the actual native attachment (possibly NON-U-closed).
Restrict this map to ANY exact induced weak test F=C|S: closed-test
protection survives precomposition with the induced inclusion S->C.

The finite private-active line index set associated with the original
test F consists of precisely the line indices whose private exterior
contains some image of one of its ORIGINAL test vertices.
If this finite index set is EMPTY, no test vertex lies in any private
exterior. The already verified fully protected core-range factor
(PR #154) completes F into the fixed A∈K by composition with
the genuine protected native power-part map.

NO maximal intrinsic U-rank or prior W_j/R_j completion hypothesis is
required for this result. In particular it gives a real native
nonmaximal-rank completion branch, unlike the older PR #152.

The branch with nonzero active indices (including nonmaximal-rank
sources), and the transverse root coherence required to finish the
higher-rank Ramsey theorem, remain open.
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

/-- Let C be ANY source Picture with its already protected projection
into the REAL native attachment. If the exact weak induced test S
visits no private exterior copy indices, then S has a corrected
K-completion in original A for EVERY intrinsic rank.

Neither the full Picture C nor temporary native attachment is assumed
U-closed by this lemma: protection of the given C-map is sufficient. -/
theorem native2019_protected_exact_weak_empty_active_has_A_completion
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
    (S : Finset U)
    (hNoActive :
      native2019_exact_active_index_finset (Old.support alpha)
        (fun x : (↑S : Set U) => p x.1) = ∅) :
    HasInducedClosedUKCompletion K rules
      (Source.induce (↑S : Set U)) := by
  classical
  let W : Set U := (↑S : Set U)
  let pS : W → Vertex (Old.support alpha)
      (W := NonInduced.Vertex (Old.restrict alpha) N) (I := I) :=
    fun x => p x.1
  have hpAbstract : IsClosedUHomomorphismEmbedding rules Source
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  have hpS : IsInducedClosedUHomomorphismEmbedding rules
      (Source.induce W)
      (attach Old.toRelStructure (Old.support alpha)
        (power (Old.restrict alpha) N).toRelStructure
        (closureLineMaps Old alpha A hRestricted lines)) pS :=
    IsClosedUHomomorphismEmbedding.toInducedClosed
      (hpAbstract.precomp_embedding (inclusion Source W))
  have hNoActiveP :
      native2019_exact_active_index_finset
        (Old.support alpha) pS = ∅ :=
    hNoActive
  have hNoPrivate : ∀ x : W, ∀ i : I,
      ¬ OutsideAt
        (W := NonInduced.Vertex (Old.restrict alpha) N)
        (I := I) (Old.support alpha) i (pS x) := by
    intro x i hOut
    have hi :
        i ∈ native2019_exact_active_index_finset
          (Old.support alpha) pS :=
      (native2019_mem_exact_active_index_iff
        (Old.support alpha) pS i).mpr ⟨x, hOut⟩
    simp [hNoActiveP] at hi
  exact native2019_protected_zero_active_has_A_completion
    (Source.induce W) Old alpha A hAK hAIrred
    hRestricted hPower lines pS hpS hNoPrivate

end AllThoseRamseyClasses.Published
