import AllThoseRamseyClasses.Published.TrackCSelectedWeakPositiveOnClosed
import AllThoseRamseyClasses.Published.TrackCNativeEHNExactProtectedImage
import PartiteConstruction.Functional.TrackCExactNativeFullTarget

/-!
# Track C: selected SAME H-target completion of small native closed tests

This module combines the verified exact protected test geometry #1146,
the positive chosen H-target witness (#1235 parent), and the exact
full tagged-to-partial H target map (Partite #704 dependency).

Fix a genuinely closed finite native test T inside a second native
EHN B-cover D, and the LITERAL S=q[T] inside the actual final
B-covered U-closed OLD candidate C. Given one selected relative OLD
H completion f_S:C.induce S -> tag(Target), the same composite map
h_T=f_S o q|T is a source-defined positive original-partial map to
Target AND has a full genuine-partial embedding on every original
native irreducible full E-copy in the exact closed T.

In particular, the positivity and full-test components use ONE
target, ONE map and ONE source carrier. No generated hull, no rank
budget, and no global full EHN map. The source D and its native
decoder are assumed no-defined-empty only through the actual
NoDefinedEmptyValues(P) premise; the selected Target is a genuine
Option(Set) partial structure and may have defined-empty operations
elsewhere.

The stronger rich defined-empty SOURCE theorem will use the verified
faithful Dom/Empty EHN HE #697 and needs the corresponding rich actual
OLD U-test dictionary. This result does not assert the final
intrinsic class-local axiom, just its exact same-witness completion
input in the native nonempty-valued branch.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure
open StructuralRamsey.Structure.TrackENativePartialFullFaithfulness

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V Q X Y Z : Type v}

/-- The SAME selected OLD relative completion f_S is full on
the exact original native irreducible E-copy, when restricted
along the native EHN q and the closed source T.

The embedding target is the SAME genuine H Target chosen in f_S.
The underlying map is literally f_S o q o e and the image is
not replaced by a generated closure hull. -/
theorem genuineTagged2019_selectedWeakCompletion_fullOnNativeIrred
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {R : Type v}
      (Test : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) R),
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hNoEmpty : NoDefinedEmptyValues (wholeMaskOriginalDecode C))
    (D : Structure L X) (q : X → V)
    (hq : D.IsEHNHomomorphismEmbedding
      ((wholeMaskOriginalDecode C).collapseDomain) q)
    (T : Finset X) (hT : D.IsClosed (↑T : Set X))
    (Target : PartialSetStructure L Y) (targetPart : Y → Parts)
    [Finite Y]
    (hTrans : FibreTransversal Target targetPart)
    (f : (↑(T.image q) : Set V) → Y)
    (hf : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑(T.image q) : Set V))
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f)
    (E : Structure L Z) (hE : E.Irreducible)
    (e : Structure.Embedding E (D.induce (↑T : Set X) hT)) :
    ∃ k : PartialSetStructure.Embedding E.toNonemptyPartial Target,
      ∀ z : Z,
        k.toFun z =
          f (exactFinsetImageMap q T (e.toFun z)) := by
  classical
  let eWhole : Structure.Embedding E D :=
    (Structure.inclusion D (↑T : Set X) hT).comp e
  have hImageS :
      ∀ z : Z, q (eWhole.toFun z) ∈ (↑(T.image q) : Set V) := by
    intro z
    change q (e.toFun z).1 ∈ T.image q
    exact Finset.mem_image.mpr
      ⟨(e.toFun z).1, (e.toFun z).2, rfl⟩
  obtain ⟨g, hg, jTag, hjTag⟩ :=
    genuineTagged2019_EHN_irredTest_protected_by_weakCompletion
      C Base basePart hC hPos hCover D q hq
      (↑(T.image q) : Set V)
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f hf
      E hE eWhole hImageS
  obtain ⟨k, hk⟩ :=
    wholeMaskCovered_exactNativeTest_toFullPartialTarget
      C Base basePart hC hPos hCover hNoEmpty
      E g Target targetPart hTrans jTag
  refine ⟨k, ?_⟩
  intro z
  have heq :
      (⟨q (eWhole.toFun z), hImageS z⟩ :
        (↑(T.image q) : Set V)) =
      exactFinsetImageMap q T (e.toFun z) := by
    apply Subtype.ext
    rfl
  calc
    k.toFun z = jTag.toFun ⟨g.toFun z, ⟨z, rfl⟩⟩ :=
      hk z
    _ = f ⟨q (eWhole.toFun z), hImageS z⟩ := hjTag z
    _ = f (exactFinsetImageMap q T (e.toFun z)) :=
      congrArg f heq

/-- Selected same-witness original-partial local completion on
a genuinely native CLOSED T of at most the original n vertices:
positive on the whole T, part-preserving, and FULL on every native
irreducible test E within T, into the very SAME Target and map.

The cardinal cutoff is not needed as a separate hypothesis here:
it enters only when a selected f_S is obtained from the ambient
n-small OLD completion premise with S=q[T], |S|≤|T|≤n. -/
theorem genuineTagged2019_selectedWeakCompletion_nativeHEOnClosedT
    (C : RelStructure
      ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L Q) (basePart : Q → Parts)
    (hC : IsUClosed
      ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {R : Type v}
      (Test : RelStructure
        ((L.withParts Parts).wholeMaskTagLanguage Parts) R),
      IsUClosed
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible
        ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (hNoEmpty : NoDefinedEmptyValues (wholeMaskOriginalDecode C))
    (D : Structure L X) (q : X → V)
    (hq : D.IsEHNHomomorphismEmbedding
      ((wholeMaskOriginalDecode C).collapseDomain) q)
    (partD : X → Parts)
    (hqParts : ∀ x : X,
      wholeMaskCoveredPart C Base basePart hC hCover (q x) = partD x)
    (T : Finset X) (hT : D.IsClosed (↑T : Set X))
    (Target : PartialSetStructure L Y) (targetPart : Y → Parts)
    [Finite Y]
    (hTrans : FibreTransversal Target targetPart)
    (f : (↑(T.image q) : Set V) → Y)
    (hf : IsInducedClosedUHomomorphismEmbedding
      ((L.withParts Parts).wholeMaskClosureRules Parts)
      (C.induce (↑(T.image q) : Set V))
      (wholeMaskTagExpansion
        (withPartsWholeMaskOld Target targetPart)) f) :
    ∃ hTpartial : (D.toNonemptyPartial).IsClosed (↑T : Set X),
      IsOriginalPartialHomomorphism
        (D.toNonemptyPartial.induceClosed (↑T : Set X) hTpartial)
        Target (f ∘ exactFinsetImageMap q T) ∧
      (∀ x : (↑T : Set X),
        targetPart ((f ∘ exactFinsetImageMap q T) x) = partD x.1) ∧
      (∀ {R : Type v} (E : Structure L R),
        E.Irreducible →
        ∀ e : Structure.Embedding E (D.induce (↑T : Set X) hT),
          ∃ k : PartialSetStructure.Embedding
            E.toNonemptyPartial Target,
            ∀ z : R,
              k.toFun z =
                f (exactFinsetImageMap q T (e.toFun z))) := by
  classical
  have hTpartial : D.toNonemptyPartial.IsClosed (↑T : Set X) :=
    (D.toNonemptyPartial.isClosed_iff_collapseDomain_isClosed
      (↑T : Set X)).mpr (by
        simpa only [Structure.toNonemptyPartial_collapseDomain] using hT)
  have hqPartial : IsOriginalPartialHomomorphism
      D.toNonemptyPartial (wholeMaskOriginalDecode C) q :=
    hq.toPartialTargetOfNoDefinedEmpty hNoEmpty
  obtain ⟨hPosPart, hPart⟩ :=
    genuineTagged2019_selectedWeakCompletion_positiveOnClosedT
      C Base basePart hC hPos hCover
      D.toNonemptyPartial partD q hqPartial hqParts
      T hTpartial Target targetPart f hf
  refine ⟨hTpartial, hPosPart, hPart, ?_⟩
  intro R E hE e
  exact genuineTagged2019_selectedWeakCompletion_fullOnNativeIrred
    C Base basePart hC hPos hCover hNoEmpty
    D q hq T hT Target targetPart hTrans
    f hf E hE e

end AllThoseRamseyClasses.Published
