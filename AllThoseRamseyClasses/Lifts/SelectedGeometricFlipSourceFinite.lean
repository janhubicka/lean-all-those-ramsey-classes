import AllThoseRamseyClasses.Lifts.SelectedGlobalFlipGeometricWitness
import AllThoseRamseyClasses.Lifts.GeometricGlobalFreeDiagram
import AllThoseRamseyClasses.Lifts.GeometricFlipGlobalSymbolFromBoundaries

/-!
# Actual canonical source flips have finite carriers

The original finite forbidden-family construction uses source witnesses
from finite forbidden structures.  The selected global canonical flip
does not export a `Finite` instance for the new source carrier,
although the replacement Q is a genuine selected finite geometric
piece and the complement is an induced substructure of the old
finite source.

Finiteness is a SOURCE fact independent of EHN weak target maps:
* a selected rooted pattern has a full rooted isomorphism to an
  actual piece of a FINITE forbidden witness; its carrier is finite;
* a full native functional free amalgam of two finite sides has a
  finite carrier, since every vertex lies in one of the two full
  side images, including all nullary-function values;
* hence the new full source in an actual selected global flip is
  finite without an additional axiom that F only contains finite
  structures.

These lemmas provide the finite-new-source instance required by
the conditional global-symbol endgame (#795, #796) from its REAL
flip inputs. They do not establish its geometric outer-boundary
hypotheses, source-map injectivity or unrestricted Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every genuinely selected forbidden geometric rooted pattern
has finite carrier, because its full rooted isomorphism embeds
into a finite member of the forbidden family. -/
theorem finiteCarrier_of_selectedGeometricRootedPattern
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {n : ℕ} (P : FunctionalRootedPattern.{u,0} L n)
    (hP : P ∈ forbiddenGeometricFunctionalPieces F n) :
    Finite P.Carrier := by
  classical
  obtain ⟨Z, Source, hFinite, _hForbidden, d, ⟨e⟩⟩ := hP
  letI : Finite Z := hFinite
  exact Finite.of_injective
    (fun p : P.Carrier => (e.equiv p).1)
    (Subtype.val_injective.comp e.equiv.injective)

/-- A full rooted extension representing an actually selected
forbidden geometric piece is finite.  This is stronger than
assuming an arbitrary profile-equivalent root extension is finite:
that assumption is false without an actual selected witness. -/
theorem finiteCarrier_of_selectedFunctionalRootExtension
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {n : ℕ} (Root : Structure L (Fin n))
    (P : FunctionalRootExtension Root)
    (hP :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        Root (Equiv.refl (Fin n)) P) ∈
        forbiddenGeometricFunctionalPieces F n) :
    Finite P.Carrier :=
  finiteCarrier_of_selectedGeometricRootedPattern F
    (FunctionalRootExtension.toEnumeratedRootedPattern
      Root (Equiv.refl (Fin n)) P) hP

/-- A full native functional free amalgam of two finite sides is
finite, irrespective of any weak EHN map or forbidden-family
membership.  This only uses exact SOURCE coverage by the sides. -/
theorem fullFunctionalFreeAmalgam_carrier_finite
    {H E B W : Type}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    [Finite E] [Finite B]
    (hFree : Structure.IsFreeAmalgam sL sR iL iR) :
    Finite W := by
  classical
  let f : E ⊕ B → W := Sum.elim iL iR
  have hSurj : Function.Surjective f := by
    intro w
    rcases hFree.covers w with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨Sum.inl a, ha.symm⟩
    · exact ⟨Sum.inr b, hb.symm⟩
  exact Finite.of_surjective f hSurj

/-- An ACTUAL selected global inner flip of a geometric piece in
a finite old source necessarily yields a finite new FULL source.
No separate finiteness axiom for F is needed.

The selected-piece witness is indispensable: arbitrary
profile-equivalent full rooted extensions need not be finite. -/
theorem finiteSource_of_selectedGeometricFlip
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V : Type} [Finite V]
    (Old : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData Old n)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hQ :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old d).root
        (Equiv.refl (Fin n)) Q) ∈
          forbiddenGeometricFunctionalPieces F n)
    {W : Type} (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iE) :
    Finite W := by
  letI : Finite Q.Carrier :=
    finiteCarrier_of_selectedFunctionalRootExtension F
      (geometricGlobalFunctionalChart Old d).root Q hQ
  letI : Finite (geometricGlobalComplementChart Old d).Carrier :=
    Finite.of_injective
      (fun b : (geometricGlobalComplementChart Old d).Carrier =>
        (b : V))
      Subtype.val_injective
  exact fullFunctionalFreeAmalgam_carrier_finite hFree


/-- The GLOBAL old-outer-symbol theorem applies to an ACTUAL
genuinely selected replacement even if its source carrier was
returned existentially without a Finite instance: finite old source
and finite selected Q plus literal full-native amalgamation suffice.

The exact new outer geometry is still supplied explicitly. The
conclusion packages the DERIVED finite-source certificate along
with the genuine selected new geometric piece and the unchanged
global 2019 canonical relation symbol. -/
theorem selectedGeometricFlip_globalSymbol_of_exactBoundaries
    (F : ∀ {Z : Type}, Structure L Z → Prop)
    {V W : Type} [Finite V]
    (Old : Structure L V) (hFOld : F Old)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (hInnerComponent :
      functionalComponentFrom Old (Set.range d.roots) d.left ⊆
        geometricPieceVertices Old P)
    (hOuterRootOutside : ∀ i : Fin n,
      P.roots i ∉ functionalComponentFrom Old
        (Set.range d.roots) d.left)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (hSelected :
      (FunctionalRootExtension.toEnumeratedRootedPattern
        (geometricGlobalFunctionalChart Old d).root
        (Equiv.refl (Fin m)) Q) ∈
          forbiddenGeometricFunctionalPieces F m)
    (hEq : (functionalDiagramPieceSetoid
      (geometricGlobalFunctionalChart Old d).root F).r
        (geometricGlobalFunctionalChart Old d).ext Q)
    (New : Structure L W) (hFNew : F New)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding
      iQ iE)
    (roots : Fin n → W)
    (hRootCoordinates : ∀ i : Fin n,
      roots i =
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier))
    (x y : {w : W // w ∉ Set.range roots})
    (hSeparated : ¬ ReachOutside New.graph (Set.range roots) x y)
    (hLeftBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) x)) =
          Set.range roots)
    (hRightBoundary :
      New.functionClosure
        (gaifmanNeighborhood New.graph
          (componentFrom New.graph (Set.range roots) y)) =
          Set.range roots)
    (hExactContext :
      (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' (oldOuterContextInInnerComplement Old P d)) =
        Set.range roots ∪
          componentFrom New.graph (Set.range roots) x)
    (hn : 0 < n) :
    ∃ (hFiniteNew : Finite W)
      (Pnew : GeometricFunctionalPieceData New n),
      (∀ i : Fin n, Pnew.roots i =
        iE (⟨P.roots i, hOuterRootOutside i⟩ :
          (geometricGlobalComplementChart Old d).Carrier)) ∧
      geometricGlobalPieceSymbol F Old
        (inferInstance : Finite V) hFOld P hn =
      geometricGlobalPieceSymbol F New hFiniteNew hFNew Pnew hn := by
  let hFiniteNew : Finite W :=
    finiteSource_of_selectedGeometricFlip
      F Old d Q hSelected New iQ iE hFree
  letI : Finite W := hFiniteNew
  obtain ⟨Pnew, hPnewRoot, hSymbol⟩ :=
    geometricFlip_globalPieceSymbol_of_exactOppositeBoundaries
      F Old hFOld P d hInnerRoot hInnerComponent
      hOuterRootOutside Q hEq New hFNew iQ iE hFree
      roots hRootCoordinates x y hSeparated
      hLeftBoundary hRightBoundary hExactContext hn
  exact ⟨hFiniteNew, Pnew, hPnewRoot, hSymbol⟩

end AllThoseRamseyClasses.Lifts
