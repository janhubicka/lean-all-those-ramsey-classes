import AllThoseRamseyClasses.Published.FunctionalWholeMaskProfileSparseWitness2019
import AllThoseRamseyClasses.Published.GeneratedClosureProfileBoundary2019
import PartiteConstruction.Functional.WholeMaskClosednessDictionary2019

/-!
A finite profiled weak common root has a compatible closed boundary.
This is the verified 2019 profile-boundary construction specialized
to the genuine partial-function complete-mask language. The root
carrier is unchanged; the generated closed boundary is a target-side
witness and is genuinely closed under source partial functions.
-/

namespace AllThoseRamseyClasses.Published
open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

theorem functionalWholeMask2019_common_weak_root_functional_boundary
    {UB H Y : Type w} [Finite UB] [Fintype H]
    (Base : PartialSetStructure L UB) (part : UB → Parts)
    (hPos : L.PositiveFuncArity)
    (hTrans : FibreTransversal Base part)
    {K : StructureClass (L := L.wholeMaskTagLanguage Parts)}
    (hBK : K (functionalWholeMask2019Canonical Base part))
    (hHer : ClosedUHereditary K (L.wholeMaskClosureRules Parts))
    (Right : RelStructure (L.wholeMaskTagLanguage Parts) Y)
    (Common : RelStructure
      (closureProfileLanguage2019
        (L.wholeMaskClosureRules Parts)
        (functionalWholeMask2019Canonical Base part)) H)
    (sL : Embedding Common
      (closureProfileExpansion2019
        (L.wholeMaskClosureRules Parts)
        (functionalWholeMask2019Canonical Base part)
        (functionalWholeMask2019Canonical Base part)))
    (sR : Embedding Common
      (closureProfileExpansion2019
        (L.wholeMaskClosureRules Parts)
        (functionalWholeMask2019Canonical Base part) Right)) :
    ∃ (S : Set UB),
      Base.IsClosed S ∧
      ∃ (aL : Embedding
        ((functionalWholeMask2019Canonical Base part).induce S)
        (functionalWholeMask2019Canonical Base part))
        (aR : Embedding
        ((functionalWholeMask2019Canonical Base part).induce S)
        Right)
        (q : H → S),
        IsUClosed (L.wholeMaskClosureRules Parts)
          ((functionalWholeMask2019Canonical Base part).induce S) ∧
        K ((functionalWholeMask2019Canonical Base part).induce S) ∧
        (∀ x : H, aL (q x) = sL x) ∧
        (∀ x : H, aR (q x) = sR x) := by
  classical
  obtain ⟨S, aL, aR, q, hClosed, hK, hQL, hQR⟩ :=
    closureProfile2019_common_weak_root_closed_boundary
      (functionalWholeMask2019Canonical Base part) Right
      (functionalWholeMask2019_canonical_UClosed Base part hTrans)
      hBK hHer Common sL sR
  have hTagged : IsUClosed (L.wholeMaskClosureRules Parts)
      (functionalWholeMask2019Canonical Base part) :=
    functionalWholeMask2019_canonical_UClosed Base part hTrans
  have hUSub : IsUSubstructure (L.wholeMaskClosureRules Parts)
      (functionalWholeMask2019Canonical Base part) S :=
    (hTagged.induce_iff_USubstructure S).mp hClosed
  have hFunctionClosed : Base.IsClosed S :=
    (Base.isClosed_iff_wholeMaskTagged_isUSubstructure
      part hPos hTrans S).mpr hUSub
  exact ⟨S, hFunctionClosed, aL, aR, q, hClosed, hK, hQL, hQR⟩

end AllThoseRamseyClasses.Published
