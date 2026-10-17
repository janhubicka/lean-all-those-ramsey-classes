import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor
import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam

/-!
# The whole function-closed common-root component factors to one witness

To bypass the printed Section 3 multicomponent Claim 2 for
BOUNDED forbidden families, one can consider a different lift
whose symbols index ALL actual closed-root component pieces,
not only pieces with minimal separating roots.

For a weak forbidden map f : Source -> A ⊕_X B, set
S := f^{-1}(X). The existing weak-root theorem proves that S
is function-closed. Choose ANY vertex x mapping A-only, and
let C be its WHOLE Gaifman component of Source minus S.
Every vertex of C maps A-only; each vertex of S maps to X.

Hence the exact full induced functional piece on S ∪ C maps
weakly into A. Its map on the COMPLETE (possibly reducible)
root S factors through X, even if multiple source roots have
identical target images. This is independent of minimal cuts
and of the number of B-only source components.

It supplies the actual left-side realization/root coordinates
needed by an auxiliary full-closed-component predicate.
Such a predicate's global finiteness and precompactness have
not yet been established for arbitrary regular infinite
forbidden families.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- The ENTIRE native full functional component piece over the
large closed root S=f^{-1}(X) has a weak EHN factorization into
the left witness. Moreover ALL its root coordinates factor
through the full induced common-root structure X.

No minimal-separator assumption, weak-map injectivity or
one-right-component condition is required. -/
theorem weakSource_wholeCommonRootLeftComponent_factor
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W)
    (hf : Source.IsEHNHomomorphismEmbedding Whole f)
    (x : U)
    (hx : x ∈ weakFreeLeftPart
      (sL := sL) (iL := iL) f) :
    let S : Set U :=
      weakFreeRootPart (sL := sL) (iL := iL) f
    let hS : Source.IsClosed S :=
      weakFreeRootPart_isClosed
        (sL := sL) (iL := iL) f hf.1
    let root : {z : U // z ∉ S} := ⟨x, hx.2⟩
    ∃ pLeft : functionalComponentUnion Source S root → E,
      (functionalComponentInduce Source S hS root).IsEHNHomomorphismEmbedding
        Left pLeft ∧
      (∀ z, iL (pLeft z) = f z.1) ∧
      ∃ xsX : S → H,
        ∀ r : S,
          pLeft (componentRootToPiece Source S hS root r) =
            sL (xsX r) := by
  classical
  dsimp
  let S : Set U := weakFreeRootPart (sL := sL) (iL := iL) f
  let hS : Source.IsClosed S :=
    weakFreeRootPart_isClosed
      (sL := sL) (iL := iL) f hf.1
  let root : {z : U // z ∉ S} := ⟨x, hx.2⟩
  have hImage : ∀ z : functionalComponentUnion Source S root,
      ∃ a : E, f z.1 = iL a := by
    intro z
    rcases z.2 with hzS | hzC
    · obtain ⟨r, hr⟩ := hzS
      exact ⟨sL r, hr.symm⟩
    · exact (weakFreePartition_component_left
        hfree f hf.1 root hx hzC).1
  have hPiece :
      (functionalComponentInduce Source S hS root).IsEHNHomomorphismEmbedding
        Whole (fun z => f z.1) :=
    hf.comp
      (functionalComponentEmbedding Source S hS root).isEHNHomomorphismEmbedding
  obtain ⟨pLeft, hpLeft, hMap⟩ :=
    ehnHomomorphismEmbedding_factor_full_side
      hPiece iL hImage
  have hRootExists (r : S) :
      ∃ a : H,
        pLeft (componentRootToPiece Source S hS root r) =
          sL a := by
    obtain ⟨a, ha⟩ := r.2
    refine ⟨a, iL.injective ?_⟩
    calc
      iL (pLeft (componentRootToPiece Source S hS root r)) =
          f r.1 := hMap _
      _ = iL (sL a) := ha.symm
  choose xsX hCoords using hRootExists
  exact ⟨pLeft, hpLeft, hMap, xsX, hCoords⟩

end AllThoseRamseyClasses.Lifts
