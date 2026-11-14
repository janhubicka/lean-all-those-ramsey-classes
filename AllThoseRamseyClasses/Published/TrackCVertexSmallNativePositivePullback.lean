import AllThoseRamseyClasses.Published.FunctionalWithParts2019ClosedNativeLocal
import PartiteConstruction.Functional.WholeMaskCoveredTaggedWeakLocalMap2019

/-!
# Track C: positive original partial completion of a CLOSED n-vertex source

An actual U-closed B-covered tagged 2019 candidate C has H-valued
relative completions of all exact OLD weak tests of at most n vertices.
A genuine partial source D maps by an ORIGINAL source-defined
homomorphism q into the actual decoded P. For a function-CLOSED
T ⊆ D of size at most n, use the literal image S=q[T], not its hull.
Complete C.induce S into a genuine H-target.

The exact-image partial weak restriction of q composes with the
checked exact OLD-to-functional completion map. Closedness of T
identifies the weak D restriction with the original full
function-closed induced structure. Values include defined empty.

This is the POSITIVE half of local H-completion only. Full test
protection is separate and uses the verified actual U-test geometry.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V X W : Type w}

/-- A genuine closed n-small T in an arbitrary partial source D has
a positive, part-preserving original-2019 H-completion on T exactly.
The test image S=q[T] is not assumed closed; its card is ≤n. -/
theorem genuineTagged2019_smallClosedNative_positiveCompletion_of_exactWeakImage
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L W) (basePart : W → Parts)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Y : Type w}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (n : ℕ)
    (hSmall : ∀ S : Finset V, S.card ≤ n →
      HasGenuinePartiteTagged2019RelativeCompletion H
        (C.induce (↑S : Set V)))
    (D : PartialSetStructure L X) [Finite X]
    (partD : X → Parts) (q : X → V)
    (hq : IsOriginalPartialHomomorphism D (wholeMaskOriginalDecode C) q)
    (hqParts : ∀ x : X,
      wholeMaskCoveredPart C Base basePart hC hCover (q x) = partD x)
    (T : Finset X)
    (hT : D.IsClosed (↑T : Set X))
    (hTCard : T.card ≤ n) :
    ∃ (Y : Type w) (_ : Finite Y)
      (Target : PartialSetStructure L Y) (targetPart : Y → Parts),
      H Target targetPart ∧ FibreTransversal Target targetPart ∧
      ∃ f : (↑T : Set X) → Y,
        IsOriginalPartialHomomorphism (D.induceClosed (↑T : Set X) hT)
          Target f ∧
        (∀ x : (↑T : Set X), targetPart (f x) = partD x.1) := by
  classical
  let S : Finset V := T.image q
  have hSCard : S.card ≤ n :=
    (Finset.card_image_le).trans hTCard
  obtain ⟨Y, hY, Target, targetPart, hTarget, hTrans,
    _hIrred, f, hf⟩ := hSmall S hSCard
  let qT : (↑T : Set X) → (↑S : Set V) :=
    fun x => ⟨q x.1,
      Finset.mem_image.mpr ⟨x.1, x.2, rfl⟩⟩
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
  refine ⟨Y, hY, Target, targetPart, hTarget, hTrans,
    (f ∘ qT), hClosedHom, ?_⟩
  intro x
  calc
    targetPart ((f ∘ qT) x) =
        wholeMaskCoveredPart C Base basePart hC hCover (q x.1) :=
      hLocalParts (qT x)
    _ = partD x.1 := hqParts x.1

end AllThoseRamseyClasses.Published
