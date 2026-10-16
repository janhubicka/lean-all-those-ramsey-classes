import AllThoseRamseyClasses.Lifts.GlobalPieceFixedRootBridge
import AllThoseRamseyClasses.Lifts.FreeAmalgamSideIso
import AllThoseRamseyClasses.Lifts.FreeAmalgamRootReparam
import AllThoseRamseyClasses.Lifts.FunctionalRootedIsoEmbedding

/-!
# Every selected forbidden piece has an incompatible rooted complement

The missing nonempty-profile lemma for the global piece quotient in the
2019 Section 3 lift. A selected finite forbidden piece is, by definition,
root-isomorphic to one cut out of a finite forbidden source A by a
minimal function-closed separator R.

The original forbidden source is already a FULL functional free amalgam
of R ∪ C and V \\ C over R. The supplied root-preserving isomorphism
replaces its first side by the selected representative. The ordered
enumeration transports the full root onto the exact standard Fin n
root of the selected chart. Its complementary side is then an
incompatible rooted TEST, not required to be a forbidden piece.

Consequently every selected global piece class has NONEMPTY
incompatibility profile. Combined with
`globalFunctionalPiece_equiv_forces_root_eq`, this ensures that
globally equivalent selected pieces have exactly the same complete
functional root structure, not merely the same root cardinality.
No isomorphism-closure axiom on the forbidden family is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}} {n : ℕ}

/-- Every genuine selected finite forbidden piece has at least one
rooted test for which its full functional free amalgam is forbidden
(up to a full isomorphism). The test is explicitly built from the
closed complementary side of its finite forbidden witness. -/
theorem selectedFunctionalChart_has_forbidden_complement
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P : SelectedFunctionalChart F n) :
    ∃ T : FunctionalRootChart.{u} L n,
      FunctionalRootChart.Incompatible F P.1 T := by
  classical
  have hSelected : IsForbiddenGeometricFunctionalPiece F P.1.pattern :=
    P.2
  obtain ⟨W, A, _hFinite, hA, d, ⟨iso⟩⟩ := hSelected
  let R : Set W := Set.range d.roots
  let hR : A.IsClosed R := d.minimal.1
  let geoRoot : Structure L R := closedCutRoot A R hR
  let G : FunctionalRootedPattern L n :=
    geometricFunctionalRootedPattern A d
  let e : Structure.Embedding P.1.ext.str (geometricFunctionalPiece A d) :=
    iso.toFullEmbedding
  let oldRootIn : Structure.Embedding geoRoot (geometricFunctionalPiece A d) :=
    componentRootToPiece A R hR d.left
  let oldCompIn : Structure.Embedding geoRoot
      (functionalComponentComplementInduce A R hR d.left) :=
    componentRootToComplement A R hR d.left
  let leftIn : Structure.Embedding (geometricFunctionalPiece A d) A :=
    functionalComponentEmbedding A R hR d.left
  let rightIn : Structure.Embedding
      (functionalComponentComplementInduce A R hR d.left) A :=
    functionalComponentComplementEmbedding A R hR d.left

  let k : Fin n → R := fun i => ⟨d.roots i, ⟨i, rfl⟩⟩
  have hk : ∀ i : Fin n,
      (e.comp P.1.ext.rootEmbedding) i = oldRootIn (k i) := by
    intro i
    change iso.toFullEmbedding (P.1.pattern.root i) = G.root i
    exact iso.toFullEmbedding_root i
  let rootIso : Structure.Embedding P.1.root geoRoot :=
    (e.comp P.1.ext.rootEmbedding).factorWithMap oldRootIn k hk
  have hRootOnto : Function.Surjective rootIso := by
    intro r
    obtain ⟨i, hi⟩ := r.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    change d.roots i = r.1
    exact hi

  have hFree0 :
      Structure.IsFreeAmalgam oldRootIn oldCompIn leftIn rightIn :=
    component_isFreeAmalgam A R hR d.left
  have hFree1 :
      Structure.IsFreeAmalgam
        (oldRootIn.comp rootIso) (oldCompIn.comp rootIso)
        leftIn rightIn :=
    freeAmalgam_precompose_root_onto hFree0 rootIso hRootOnto
  have hRootCommutes : ∀ i : Fin n,
      e (P.1.ext.rootEmbedding i) =
        (oldRootIn.comp rootIso) i := by
    intro i
    exact hk i
  have hFree2 :
      Structure.IsFreeAmalgam
        P.1.ext.rootEmbedding (oldCompIn.comp rootIso)
        (leftIn.comp e) rightIn :=
    freeAmalgam_precompose_left_iso hFree1 e
      iso.toFullEmbedding_surjective
      P.1.ext.rootEmbedding hRootCommutes

  let T : FunctionalRootChart.{u} L n := {
    root := P.1.root
    ext := {
      Carrier := Set.compl (functionalComponentFrom A R d.left)
      str := functionalComponentComplementInduce A R hR d.left
      rootEmbedding := oldCompIn.comp rootIso
    }
  }
  have hDiagram :
      forbiddenFunctionalDiagram P.1.root F P.1.ext T.ext :=
    ⟨W, A, hA, leftIn.comp e, rightIn, hFree2⟩
  have hGlue :
      forbiddenFunctionalGlue P.1.root F P.1.ext T.ext :=
    (forbiddenFunctionalDiagram_iff_glue P.1.root F P.1.ext T.ext).mp
      hDiagram
  exact ⟨T, rfl, hGlue⟩

/-- There are no accidental identifications between different full
root structures in the global forbidden-piece quotient. The witness
for nonemptiness is constructed from the source, rather than being
introduced as a new class axiom. -/
theorem globalFunctionalPiece_equiv_root_eq
    (F : ∀ {W : Type}, Structure L W → Prop)
    (P Q : SelectedFunctionalChart F n)
    (hEq : (globalFunctionalPieceSetoid F n).r P Q) :
    P.1.root = Q.1.root :=
  globalFunctionalPiece_equiv_forces_root_eq F P Q hEq
    (selectedFunctionalChart_has_forbidden_complement F P)

end AllThoseRamseyClasses.Lifts
