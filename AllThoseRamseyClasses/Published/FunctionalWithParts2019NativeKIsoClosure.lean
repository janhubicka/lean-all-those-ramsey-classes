import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKStrongAmalgamTransfer
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKIso

/-!
# Track B: faithful H_K and canonical tagged K_H are isomorphism closed

The corrected 2019 two-pass Ramsey theorem requires the canonical
K_H class to be isomorphism invariant, not merely a raw predicate
on carrier-polymorphic structures. The class constructed from
faithful native K-systems already has this property when K is
a native hereditary free-amalgamation class.

The critical semantic step is to check that an arbitrary genuine
partial source A with a FULL part-preserving embedding into the
faithful target B=BN.toNonemptyPartial has NO independently
DEFINED-empty function values. A defined-empty source would have
to map to a defined-empty target, which the faithful native
representation cannot possess. Hence A is literally its own
collapseDomain→toNonemptyPartial roundtrip on the SAME carrier.

Using the full partial embedding's native collapse gives an
ordinary full native embedding A.collapseDomain→BN.toStructure.
Native heredity then places A.collapseDomain in K, and output
transversality of the partite source follows by reflecting
relations/function incidences and part labels through that
injective full embedding. Thus A itself belongs to faithful H_K.

Finally apply the verified canonical 2019 isomorphism-closure
transfer; this discharges one more explicit class hypothesis of
the corrected two-pass 2019 theorem, without using any
semi-closed local completion or arbitrary intrinsic weak test.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The faithful original class H_K is closed under FULL
part-preserving subembeddings into faithful K-members, and in
particular under finite part-preserving isomorphisms.

The proof explicitly protects the distinction between
`none` and `some ∅`: a genuinely defined-empty value in
A would map to a defined-empty value in the faithful native
target, which is impossible. Thus the source is also a faithful
native image; no arbitrary genuine partial object is collapsed
while pretending to preserve its definedness.

The native `FreeAmalgamationClass.hereditary` is the ONLY
native K-class hypothesis, and no surjectivity of the full
embedding is actually needed. -/
theorem nativeKFaithfulH_isomorphismClosed_of_free
    (K : Structure.StructureClass.{u,v} (L := L))
    (hK : Structure.FreeAmalgamationClass K) :
    GenuinePartiteIsomorphismClosed2019
      (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K) := by
  classical
  intro U V hU hV A partA B partB hB f _hSurj
  obtain ⟨BN, hBN, hBEq, hPartBEq⟩ := hB
  subst B
  subst partB
  have hNoDefinedEmpty :
      ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → U)
        (T : Set U), A.func F xs = some T → T.Nonempty := by
    intro F xs T hFx
    let ys : Fin (L.funcArity F) → V := f.1.toFun ∘ xs
    have hMapped :
        BN.toStructure.toNonemptyPartial.func F ys =
          some (Structure.imageSet f.1.toFun T) := by
      have h := f.1.map_func F xs
      rw [hFx] at h
      simpa only [Option.map_some] using h.symm
    have hNativeNonempty : (BN.toStructure.func F ys).Nonempty :=
      (BN.toStructure.toNonemptyPartial_defined_iff F ys).mp
        ⟨Structure.imageSet f.1.toFun T, hMapped⟩
    have hImageEq :
        BN.toStructure.func F ys = Structure.imageSet f.1.toFun T := by
      have hSome :
          some (BN.toStructure.func F ys) =
            some (Structure.imageSet f.1.toFun T) := by
        simpa [Structure.toNonemptyPartial, hNativeNonempty] using hMapped
      exact Option.some.inj hSome
    have hImageNe : (Structure.imageSet f.1.toFun T).Nonempty := by
      rw [← hImageEq]
      exact hNativeNonempty
    obtain ⟨z, hz⟩ := hImageNe
    obtain ⟨t, ht, _⟩ := hz
    exact ⟨t, ht⟩
  have hRoundtrip : A.collapseDomain.toNonemptyPartial = A := by
    cases A with
    | mk rel fn =>
      change PartialSetStructure.mk rel _ = PartialSetStructure.mk rel fn
      congr 1
      funext F xs
      cases hv : fn F xs with
      | none =>
          simp [Structure.toNonemptyPartial, PartialSetStructure.collapseDomain, hv]
      | some T =>
          have hT : T.Nonempty := hNoDefinedEmpty F xs T hv
          simp [Structure.toNonemptyPartial, PartialSetStructure.collapseDomain, hv, hT]
  let eNative : Structure.Embedding A.collapseDomain BN.toStructure := {
    toFun := f.1.toFun
    injective := f.1.injective
    map_rel_iff := f.1.map_rel_iff
    map_func := by
      intro F xs
      have h := (f.1.toCollapsedNative).map_func F xs
      simpa only [Structure.toNonemptyPartial_collapseDomain] using h
  }
  have hKA : K A.collapseDomain := hK.hereditary hBN eNative
  let AN : FunctionalPartite.System L Parts U := {
    toStructure := A.collapseDomain
    part := partA
    relTransversal := by
      intro R xs hRel i j hPart
      have hRelB : BN.toStructure.rel R (eNative ∘ xs) :=
        (eNative.map_rel_iff R xs).mpr hRel
      have hParts :
          BN.part (eNative (xs i)) = BN.part (eNative (xs j)) := by
        calc
          BN.part (eNative (xs i)) = partA (xs i) := f.2 (xs i)
          _ = partA (xs j) := hPart
          _ = BN.part (eNative (xs j)) := (f.2 (xs j)).symm
      exact eNative.injective
        (BN.relTransversal R (eNative ∘ xs) hRelB i j hParts)
    funcTransversal := by
      intro F xs y z hy hz hPart
      have hMapped := eNative.map_func F xs
      have hyB : eNative y ∈
          BN.toStructure.func F (eNative ∘ xs) := by
        rw [← hMapped]
        exact ⟨y, hy, rfl⟩
      have hzB : eNative z ∈
          BN.toStructure.func F (eNative ∘ xs) := by
        rw [← hMapped]
        exact ⟨z, hz, rfl⟩
      have hParts :
          BN.part (eNative y) = BN.part (eNative z) := by
        calc
          BN.part (eNative y) = partA y := f.2 y
          _ = partA z := hPart
          _ = BN.part (eNative z) := (f.2 z).symm
      exact eNative.injective
        (BN.funcTransversal F (eNative ∘ xs)
          (eNative y) (eNative z) hyB hzB hParts)
  }
  exact ⟨AN, hKA, hRoundtrip.symm, rfl⟩

/-- The canonical 2019 OLD complete-mask/full-root-tagged K_H
class of a native functional FreeAmalgamationClass is
ISOMORPHISM CLOSED. This is the corrected 2019
coordinated multiamalgamation class condition; no new
assumption on arbitrary K_H is introduced.

The source class is precisely H_K of faithful native
part-transversal systems; the locally finite
ambient-relative completion axiom remains separate. -/
theorem nativeKCanonicalTagged2019_isomorphismClosed_of_free
    (K : Structure.StructureClass.{u,v} (L := L))
    (hK : Structure.FreeAmalgamationClass K) :
    IsomorphismClosed2019
      (canonicalGenuineTagged2019Class
        (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)) :=
  canonicalGenuineTagged2019Class_isomorphismClosed
    (nativeKFaithfulGenuinePartiteH2019 (Parts := Parts) K)
    (nativeKFaithfulH_isomorphismClosed_of_free K hK)

end AllThoseRamseyClasses.Published
