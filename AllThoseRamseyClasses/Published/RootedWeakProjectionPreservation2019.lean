import AllThoseRamseyClasses.Published.RootedWeakSizeBase2019

/-!
# The strengthened 2019 ROOTED weak-size invariant is PRESERVED by projections

The repaired exact weak-size induction W_j(C) was too weak for the
earlier closed rank-j gluing step. The rooted alternative W_j^A(C)
requires K-completions of exact induced tests on T U a[A] for
every T of at most j vertices and every induced full copy a:A->C.

Here we prove a general and important preservation theorem:
if a finite/weak Picture C admits a corrected induced-closed
U-homomorphism-embedding p:C->D into an old Picture D satisfying
W_j^A(D), then C ALSO satisfies W_j^A(C), provided the selected
fixed A itself is intrinsically U-closed and U-irreducible.

Why this works:
* the protected map on the EMBEDDED closed U-irreducible A-test
  makes p∘a a GENUINE full embedding aD:A->D;
* the exact <=j new weak vertices T have an image p[T] of <=j
  vertices in D, even when p is globally noninjective;
* the entire exact weak source C|(T U a[A]) projects protectedly
  into the exact old weak source D|(p[T] U aD[A]);
* the rooted completion of this old source pulls back to the
  original weak source, WITHOUT closing or enlarging the source
  and without a rank budget for |A|.

This proves preservation of the stronger recursive invariant under
ANY corrected protected Picture projection. It does NOT construct
the Hales--Jewett successor Picture satisfying W_(j+1)^A, nor does
it complete arbitrary nonmaximal weak tests. These remain substantial
missing constructors; no unconditional repaired Theorem 2.18 here.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Pull back ROOTED exact weak vertex-size completability along any
corrected protected projection, without injectivity, closedness of
the new source, or an independent weak generator-hull argument.

The fixed A must be intrinsically U-closed and U-irreducible so its
actual embedded copies are protected as FULL embeddings into Old.
No extra cardinality assumption |A| <= j is imposed. -/
theorem has2019_rooted_weaksize_of_protected_projection
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD VA : Type v}
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (hAClosed : IsUClosed rules A)
    (hAUIrred : IsUIrreducible rules A)
    (p : VC → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules C D p)
    (j : ℕ)
    (hOld : Has2019RootedWeakSizeCompletions K rules D A j) :
    Has2019RootedWeakSizeCompletions K rules C A j := by
  classical
  have hpAbs : IsClosedUHomomorphismEmbedding rules C D p :=
    IsInducedClosedUHomomorphismEmbedding.toAbstract_2019 hp
  intro T a hCard
  obtain ⟨aD, haD⟩ := hpAbs.on_test A hAClosed hAUIrred a
  let I : Finset VD := T.image p
  have hICard : I.card ≤ j :=
    (Finset.card_image_le).trans hCard
  let TC : Set VC := (↑T : Set VC) ∪ Set.range a
  let ID : Set VD := (↑I : Set VD) ∪ Set.range aD
  have hRange (x : TC) : p x.1 ∈ ID := by
    rcases x.2 with hx | ⟨y, hy⟩
    · exact Or.inl (Finset.mem_image.mpr ⟨x.1, hx, rfl⟩)
    · right
      refine ⟨y, ?_⟩
      rw [hy]
      exact (haD y).symm
  have hpTC : IsClosedUHomomorphismEmbedding rules
      (C.induce TC) D (p ∘ Subtype.val) :=
    hpAbs.precomp_embedding (inclusion C TC)
  have hpID : IsClosedUHomomorphismEmbedding rules
      (C.induce TC) (D.induce ID)
      (fun x : TC => ⟨p x.1, hRange x⟩) :=
    hpTC.codRestrict ID hRange
  have hOldExact : HasClosedUKCompletion K rules (D.induce ID) :=
    (inducedClosedKCompletion_iff_abstract_2019).mp
      (hOld I aD hICard)
  have hThisExact : HasClosedUKCompletion K rules (C.induce TC) :=
    hOldExact.precomp_closedMap hpID
  exact (inducedClosedKCompletion_iff_abstract_2019).mpr hThisExact


/-- Paper-faithful convenience version: ordinary irreducibility of A,
as already required for all members of the ambient Ramsey class,
automatically implies its intrinsic U-irreducibility. Thus the
rooted-invariant projection transfer asks for no new irreducibility
hypothesis beyond the existing original proof data. -/
theorem has2019_rooted_weaksize_of_protected_projection_irreducible_A
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {VC VD VA : Type v}
    (C : RelStructure L VC)
    (D : RelStructure L VD)
    (A : RelStructure L VA)
    (hAClosed : IsUClosed rules A)
    (hAIrred : A.Irreducible)
    (p : VC → VD)
    (hp : IsInducedClosedUHomomorphismEmbedding rules C D p)
    (j : ℕ)
    (hOld : Has2019RootedWeakSizeCompletions K rules D A j) :
    Has2019RootedWeakSizeCompletions K rules C A j :=
  has2019_rooted_weaksize_of_protected_projection
    C D A hAClosed (hAIrred.isUIrreducible rules) p hp j hOld


end AllThoseRamseyClasses.Published
