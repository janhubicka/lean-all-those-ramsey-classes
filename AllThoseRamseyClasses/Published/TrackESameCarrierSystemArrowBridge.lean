import AllThoseRamseyClasses.Published.TrackEStandardFunctionalPartiteArrow

/-!
# Track E: package an ACTUAL native decoded target as a partite System

This bridge takes both distinct transversality obligations as EXPLICIT
hypotheses. It changes neither the vertex carrier nor the native Structure
nor the recovered part map. The standard FunctionalPartite.Arrow is then
exactly the existing native part-preserving arrow, on the same colourings
and full embeddings.

In the 2019 sparse-witness application, native function-fibre
transversality is treated in Track E #940, and native relation-tuple
transversality under a separate hypothesis on B in Track E #944.
Neither is inferred by this bridge. No H-membership, total-fibre
reflection, strict functional B-tree, or unrestricted 2019 theorem is
claimed here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.Structure.TrackENativePartiteFinalArrow

universe u v w
variable {L : Language.{u}} {Parts : Type v}

/-- An exact-carrier native partite System. Both required kinds of
transversality are named in the hypotheses; no replacement structure,
generated hull, or arbitrary choice of parts is introduced. -/
def sameCarrierFunctionalPartiteSystem {X : Type w}
    (D : Structure L X) (partD : X → Parts)
    (hRel : ∀ R xs, D.rel R xs → ∀ i j,
      partD (xs i) = partD (xs j) → xs i = xs j)
    (hFunc : ∀ F xs y z, y ∈ D.func F xs → z ∈ D.func F xs →
      partD y = partD z → y = z) :
    StructuralRamsey.FunctionalPartite.System L Parts X where
  toStructure := D
  part := partD
  relTransversal := hRel
  funcTransversal := hFunc

@[simp] theorem sameCarrierFunctionalPartiteSystem_toStructure
    {X : Type w}
    (D : Structure L X) (partD : X → Parts)
    (hRel : ∀ R xs, D.rel R xs → ∀ i j,
      partD (xs i) = partD (xs j) → xs i = xs j)
    (hFunc : ∀ F xs y z, y ∈ D.func F xs → z ∈ D.func F xs →
      partD y = partD z → y = z) :
    (sameCarrierFunctionalPartiteSystem D partD hRel hFunc).toStructure = D := by
  rfl

@[simp] theorem sameCarrierFunctionalPartiteSystem_part
    {X : Type w}
    (D : Structure L X) (partD : X → Parts)
    (hRel : ∀ R xs, D.rel R xs → ∀ i j,
      partD (xs i) = partD (xs j) → xs i = xs j)
    (hFunc : ∀ F xs y z, y ∈ D.func F xs → z ∈ D.func F xs →
      partD y = partD z → y = z) :
    (sameCarrierFunctionalPartiteSystem D partD hRel hFunc).part = partD := by
  rfl

/-- The CONDITIONAL final packaging step. Once the actual decoded
native target has both transversality certificates, its native
part-preserving arrow is equivalent to the standard functional partite
System arrow on the literal same target and parts. This uses the full
embedding equivalence from Track E #947, not a mere bijection of
unlabelled vertices. -/
theorem nativeArrow_iff_standardArrow_of_sameCarrierTransversal
    {VA VB VC : Type w}
    (A : StructuralRamsey.FunctionalPartite.System L Parts VA)
    (B : StructuralRamsey.FunctionalPartite.System L Parts VB)
    (D : Structure L VC) (partD : VC → Parts)
    (hRel : ∀ R xs, D.rel R xs → ∀ i j,
      partD (xs i) = partD (xs j) → xs i = xs j)
    (hFunc : ∀ F xs y z, y ∈ D.func F xs → z ∈ D.func F xs →
      partD y = partD z → y = z)
    (κ : Type*) :
    NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part D partD κ ↔
    StructuralRamsey.FunctionalPartite.Arrow A B
      (sameCarrierFunctionalPartiteSystem D partD hRel hFunc) κ := by
  let Final := sameCarrierFunctionalPartiteSystem D partD hRel hFunc
  change NativePartPreservingArrow
      A.toStructure A.part B.toStructure B.part
      Final.toStructure Final.part κ ↔
    StructuralRamsey.FunctionalPartite.Arrow A B Final κ
  exact nativePartPreservingArrow_iff_standardSystemArrow A B Final κ

end AllThoseRamseyClasses.Published
