import AllThoseRamseyClasses.Lifts.FunctionalDiagramFlip
import AllThoseRamseyClasses.Lifts.FunctionalComponentFreeAmalgam
import AllThoseRamseyClasses.Lifts.GeometricFunctionalPieces

/-!
# From a geometric separating cut to a genuine fixed-root functional chart

The main theorem's piece (R union one component) and its complementary
side now form root extensions of the SAME full functional root
structure induced on the closed cut. This is not merely a matching
ordered tuple or a relational graph root: it retains the domains and
values of every original function.

The preexisting verified `component_isFreeAmalgam` certificate shows
that the ACTUAL forbidden source is a full free amalgam of these two
extensions. This provides the geometric-to-fixed-root normalization
step needed for the Section 3 flip.

No assumption of finite carrier or minimality is needed to form a
chart for a closed cut; a geometrically selected piece supplies the
minimality separately.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The induced whole functional root structure of a closed cut. -/
abbrev closedCutRoot (A : Structure L V)
    (R : Set V) (hR : A.IsClosed R) : Structure L R :=
  A.induce R hR

/-- One connected component, together with the whole closed cut,
as an extension of the exact FUNCTIONAL root. -/
def componentPieceRootExtension
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R)
    (root : {v : V // v ∉ R}) :
    FunctionalRootExtension (closedCutRoot A R hR) where
  Carrier := functionalComponentUnion A R root
  str := functionalComponentInduce A R hR root
  rootEmbedding := componentRootToPiece A R hR root

/-- The complementary closed functional side, sharing the exact
induced root structure (not merely its vertex list). -/
def componentComplementRootExtension
    (A : Structure L V) (R : Set V)
    (hR : A.IsClosed R)
    (root : {v : V // v ∉ R}) :
    FunctionalRootExtension (closedCutRoot A R hR) where
  Carrier := Set.compl (functionalComponentFrom A R root)
  str := functionalComponentComplementInduce A R hR root
  rootEmbedding := componentRootToComplement A R hR root

/-- The ROOT-WISE, actual-source diagram exists for EVERY closed
cut and selected complementary component. Its carrier is literally
the original source V, and the two side inclusions are FULL
functional embeddings with exact overlap and no mixed incidences. -/
theorem functionalSource_hasRootChartDiagram
    (A : Structure L V) (R : Set V) (hR : A.IsClosed R)
    (root : {v : V // v ∉ R})
    (Forbidden : ∀ {W : Type v}, Structure L W → Prop)
    (hForbidden : Forbidden A) :
    forbiddenFunctionalDiagram
      (closedCutRoot A R hR) Forbidden
      (componentPieceRootExtension A R hR root)
      (componentComplementRootExtension A R hR root) := by
  refine ⟨V, A, hForbidden,
    functionalComponentEmbedding A R hR root,
    functionalComponentComplementEmbedding A R hR root, ?_⟩
  exact component_isFreeAmalgam A R hR root

/-- The root extension selected by an actual minimal separator has
exactly the geometric piece's native functional structure, on
exactly the same carrier. -/
theorem geometricPiece_rootChart_str
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    (componentPieceRootExtension A (Set.range d.roots)
      d.minimal.1 d.left).str =
      geometricFunctionalPiece A d := rfl

/-- Every genuinely forbidden geometric source comes with a
functional fixed-root chart of its piece AND its complement. -/
theorem forbiddenGeometricSource_hasRootChart
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (Forbidden : ∀ {W : Type v}, Structure L W → Prop)
    (hForbidden : Forbidden A) :
    forbiddenFunctionalDiagram
      (closedCutRoot A (Set.range d.roots) d.minimal.1)
      Forbidden
      (componentPieceRootExtension A (Set.range d.roots)
        d.minimal.1 d.left)
      (componentComplementRootExtension A (Set.range d.roots)
        d.minimal.1 d.left) :=
  functionalSource_hasRootChartDiagram A (Set.range d.roots)
    d.minimal.1 d.left Forbidden hForbidden

end AllThoseRamseyClasses.Lifts
