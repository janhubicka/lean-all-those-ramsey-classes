import AllThoseRamseyClasses.Published.TrackCVertexSmallNativePositivePullback
import PartiteConstruction.Functional.WholeMaskCoveredTaggedWeakLocalMap2019

/-!
# Track C: exact SAME selected OLD weak-completion map is the positive native map

The verified small closed-test lemma #1147 constructs an H-target
existentially. To combine its positive map with the verified
full-on-every-irreducible OLD test protection #1146, we must show
both results use the IDENTICAL target and underlying vertex map.

Fix the actual OLD source C and one chosen tagged weak completion
f_S : C.induce(q[T]) → tag(Target). This theorem proves that
the ORIGINAL closed functional source D.induceClosed(T) has a
source-defined positive map into that VERY SAME Target, whose
literal vertex map is f_S ∘ q restricted to T.

No generated closure hull is used. The exact image q[T] need not be
function-closed; the original n-vertex cardinality bound remains
unchanged in the eventual application. Defined empty values retain
their independent domain bit.

This is not the HE conclusion: that needs the SAME selected
f_S to be full on each genuine irreducible test, followed by
the exact tagged/full partial decoder, as in #1146/#704.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V X W Y : Type w}

-- Exact Finset images are classically decidable; this is not a theorem hypothesis.
private noncomputable instance (Z : Type w) : DecidableEq Z := Classical.decEq Z

/-- Restrict q to its EXACT image on T. No injectivity or
function-closedness of the image is required. -/
def exactFinsetImageMap (q : X → V) (T : Finset X) :
    (↑T : Set X) → (↑(T.image q) : Set V) :=
  fun x => ⟨q x.1, Finset.mem_image.mpr
    ⟨x.1, x.2, rfl⟩⟩

/-- The chosen induced-closed OLD completion map f_S yields
positive ORIGINAL native completion of the EXACT closed source
T, using literally the same H-target and the map f_S ∘ q|T.

This is the map-equality prerequisite for later full native
irreducible-test protection under the SAME selected f_S. -/
theorem genuineTagged2019_selectedWeakCompletion_positiveOnClosedT
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L W) (basePart : W → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Z : Type w}
      (Test : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) Z),
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (D : PartialSetStructure L X)
    (partD : X → Parts) (q : X → V)
    (hq : IsOriginalPartialHomomorphism
      D (wholeMaskOriginalDecode C) q)
    (hqParts : ∀ x : X,
      wholeMaskCoveredPart C Base basePart hC hCover (q x) = partD x)
    (T : Finset X)
    (hT : D.IsClosed (↑T : Set X))
    (Target : PartialSetStructure L Y) (targetPart : Y → Parts)
    (f : (↑(T.image q) : Set V) → Y)
    (hf : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑(T.image q) : Set V))
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f) :
    IsOriginalPartialHomomorphism
      (D.induceClosed (↑T : Set X) hT)
      Target (f ∘ exactFinsetImageMap q T) ∧
    (∀ x : (↑T : Set X),
      targetPart ((f ∘ exactFinsetImageMap q T) x) = partD x.1) := by
  classical
  let S : Finset V := T.image q
  let qT : (↑T : Set X) → (↑S : Set V) :=
    exactFinsetImageMap q T
  have hWeakMap :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce D (↑T : Set X))
        (wholeWeakInduce (wholeMaskOriginalDecode C) (↑S : Set V))
        qT :=
    hq.wholeWeakRestrict (↑T : Set X) (↑S : Set V) qT
      (fun _ => rfl)
  have hTaggedHom :
      (C.induce (↑S : Set V)).IsHomomorphism
        (wholeMaskTagExpansion
          ((Target.withParts targetPart).wholeMaskPatternGraph targetPart)) f :=
    hf.1
  obtain ⟨hLocal, hLocalParts⟩ :=
    wholeMaskOriginalDecode_weak_originalPartial_of_taggedLocalHom
      C Base basePart hC hPos hCover
      (↑S : Set V) Target targetPart f hTaggedHom
  have hComposed :
      IsOriginalPartialHomomorphism
        (wholeWeakInduce D (↑T : Set X)) Target (f ∘ qT) :=
    hLocal.comp hWeakMap
  have hClosedHom :
      IsOriginalPartialHomomorphism
        (D.induceClosed (↑T : Set X) hT)
        Target (f ∘ qT) := by
    constructor
    · exact hComposed.1
    · intro F xs U hValue
      have hWeak :
          (wholeWeakInduce D (↑T : Set X)).func F xs =
          (D.induceClosed (↑T : Set X) hT).func F xs :=
        wholeWeakInduce_func_eq_induceClosed_of_isClosed
          D (↑T : Set X) hT F xs
      exact hComposed.2 F xs U (hWeak.trans hValue)
  refine ⟨hClosedHom, ?_⟩
  intro x
  calc
    targetPart ((f ∘ qT) x) =
        wholeMaskCoveredPart C Base basePart hC hCover (q x.1) :=
      hLocalParts (qT x)
    _ = partD x.1 := hqParts x.1

end AllThoseRamseyClasses.Published
