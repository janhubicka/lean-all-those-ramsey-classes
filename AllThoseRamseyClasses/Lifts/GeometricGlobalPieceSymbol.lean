import AllThoseRamseyClasses.Lifts.GlobalFunctionalPieceLift
import AllThoseRamseyClasses.Lifts.ClosedFunctionalRoots
import AllThoseRamseyClasses.Lifts.GeometricPieceRootChart

/-!
# An actual geometric forbidden piece represents a GLOBAL lift symbol

The indexed canonical lift of the 2019 paper uses ALL equivalence
classes of genuine finite forbidden pieces, not merely the temporary
one-class language introduced for proving the fixed-root flip.

A geometrically selected piece has an exact full functional root
structure on the ordered standard carrier Fin n. It therefore
determines a selected global root chart and, at positive root widths,
a genuine relation symbol of the global expanded language.

If a weak 2019-style homomorphism-embedding realizes this piece in
an ambient structure, and its image of the ordered separator is
injective, it witnesses that very GLOBAL canonical relation.
There is no appeal to an abstract choice of representatives or a
spurious equality of full function-value fibres for weak maps.

The injectivity requirement is explicit; it must be established by
the later forbidden-image reduction before use in the unrestricted
published flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {V : Type} {n : ℕ}

/-- The full Fin n root chart carried by an actual minimal-cut
geometric forbidden source piece, including EVERY old function. -/
def geometricGlobalFunctionalChart
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    FunctionalRootChart.{u} L n := by
  let G := geometricFunctionalRootedPattern A d
  let hG : G.IsRootClosed :=
    geometricFunctionalRootedPattern_rootClosed A n d
  exact {
    root := G.rootStructure hG
    ext := {
      Carrier := G.Carrier
      str := G.str
      rootEmbedding := G.rootInclusion hG
    }
  }

/-- Its rooted-pattern presentation is literally the geometric
piece, including the original function interpretations and the
ordered root tuple. -/
theorem geometricGlobalFunctionalChart_pattern
    (A : Structure L V) (d : GeometricFunctionalPieceData A n) :
    (geometricGlobalFunctionalChart A d).pattern =
      geometricFunctionalRootedPattern A d := by
  rfl

/-- Every finite forbidden source possessing such a genuine piece
determines a SELECTED global functional chart, not merely an
arbitrary root extension. -/
def geometricGlobalSelectedChart
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) :
    SelectedFunctionalChart F n := by
  refine ⟨geometricGlobalFunctionalChart A d, ?_⟩
  change IsForbiddenGeometricFunctionalPiece F
    (geometricGlobalFunctionalChart A d).pattern
  refine ⟨V, A, hFinite, hFA, d, ?_⟩
  rw [geometricGlobalFunctionalChart_pattern]
  exact ⟨RootedPatternIso.refl _⟩

/-- The actual global relation symbol of the geometric forbidden
piece's equivalence class, at a positive root width. -/
def geometricGlobalPieceSymbol
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n) :
    GlobalFunctionalPieceSymbol F :=
  ⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n)
    (geometricGlobalSelectedChart F A hFinite hFA d)⟩

/-- The geometric source piece induces its proper GLOBAL canonical
lift relation through any WEAK rooted realization with injective
root image. In particular this is not the older single-class
temporary canonical predicate. -/
theorem geometricGlobalCanonicalRelation_of_weak
    (F : ∀ {W : Type}, Structure L W → Prop)
    (A : Structure L V) (hFinite : Finite V) (hFA : F A)
    (d : GeometricFunctionalPieceData A n) (hn : 0 < n)
    {W : Type} (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hRoots : Function.Injective (fun i : Fin n => f (d.roots i))) :
    (globalFunctionalCanonicalLift F B).rel
      (.inr (geometricGlobalPieceSymbol F A hFinite hFA d hn))
      (fun i : Fin n => f (d.roots i)) := by
  let P := geometricGlobalSelectedChart F A hFinite hFA d
  let pf : P.1.ext.Carrier → W := fun x => f x.1
  have hWeak : P.1.ext.str.IsEHNHomomorphismEmbedding B pf := by
    exact hf.comp
      (geometricFunctionalPieceEmbedding A d).isEHNHomomorphismEmbedding
  have hInj : Function.Injective
      (fun i : Fin n => pf (P.1.ext.rootEmbedding i)) := by
    change Function.Injective (fun i : Fin n => f (d.roots i))
    exact hRoots
  change (globalFunctionalCanonicalLift F B).rel
    (.inr
      (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) P⟩ :
        GlobalFunctionalPieceSymbol F))
    (fun i : Fin n => pf (P.1.ext.rootEmbedding i))
  apply (globalFunctionalCanonicalRelation_iff F B
    (⟨⟨n, hn⟩, Quotient.mk (globalFunctionalPieceSetoid F n) P⟩ :
      GlobalFunctionalPieceSymbol F)
    (fun i : Fin n => pf (P.1.ext.rootEmbedding i))).mpr
  refine ⟨hInj, P, rfl, ?_⟩
  exact ⟨pf, hWeak, fun _ => rfl⟩

end AllThoseRamseyClasses.Lifts
