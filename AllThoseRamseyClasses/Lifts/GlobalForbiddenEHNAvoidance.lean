import AllThoseRamseyClasses.Lifts.EHNFullSideFactor

/-!
# The original Section 3 forbidden-free native functional shadows

A native old-language structure belongs to Forb_HE(F) precisely when
no member of the forbidden source family admits a WEAK EHN
homomorphism-embedding into it. Only finite forbidden sources count.
This is the projection class to be homogenized by canonical lifts.

Avoidance descends along every FULL functional embedding. It is
invariant under a surjective full embedding (isomorphism), using
the verified exact EHN factorization through a full target-side
embedding. This preserves native relation and COMPLETE function
value fibres, not just positive relational incidences.

The two properties are elementary but needed explicitly to state
the exact reduct of a global regular maximal-trace age. They do
not presume that Forb_HE(F) has JEP, AP, strong amalgamation, or
a Ramsey expansion.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Finite native functional structures that avoid every
forbidden finite source under the actual EHN weak
homomorphism-embedding test. -/
def AvoidsGlobalFunctionalEHN
    (F : ∀ {W : Type}, Structure L W → Prop)
    {V : Type} (A : Structure L V) : Prop :=
  ∀ {U : Type} (Source : Structure L U),
    Finite U → F Source →
    ∀ f : U → V,
      ¬ Source.IsEHNHomomorphismEmbedding A f

/-- Forb_HE(F) is hereditary under arbitrary FULL old-language
embeddings. A weak forbidden map into the smaller structure
composes with the full embedding into the forbidden-free target. -/
theorem avoidsGlobalFunctionalEHN_of_embedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (hB : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F A := by
  intro U Source hFin hF f hf
  have hComp :
      Source.IsEHNHomomorphismEmbedding B (e ∘ f) :=
    e.isEHNHomomorphismEmbedding.comp hf
  exact (hB Source hFin hF (e ∘ f)) hComp

/-- The forbidden-free property is invariant under a surjective
FULL functional embedding. To pull a weak forbidden-source
witness back, use EHN factorization, NOT bare weak-image inclusion
(which is generally not a full embedding). -/
theorem avoidsGlobalFunctionalEHN_of_full_surjective
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (he : Function.Surjective e)
    (hA : AvoidsGlobalFunctionalEHN F A) :
    AvoidsGlobalFunctionalEHN F B := by
  intro U Source hFin hF f hf
  have hRange : ∀ x : U, ∃ a : UA, f x = e a := by
    intro x
    obtain ⟨a, ha⟩ := he (f x)
    exact ⟨a, ha.symm⟩
  obtain ⟨g, hg, _⟩ :=
    ehnHomomorphismEmbedding_factor_full_side hf e hRange
  exact (hA Source hFin hF g) hg

/-- The precise isomorphism-invariant forbidden-free class
used for the printed regular-family lift's native reduct. -/
theorem avoidsGlobalFunctionalEHN_iff_full_isomorphism
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UA UB : Type}
    {A : Structure L UA} {B : Structure L UB}
    (e : Structure.Embedding A B)
    (he : Function.Surjective e) :
    AvoidsGlobalFunctionalEHN F A ↔
      AvoidsGlobalFunctionalEHN F B := by
  constructor
  · exact avoidsGlobalFunctionalEHN_of_full_surjective F e he
  · exact avoidsGlobalFunctionalEHN_of_embedding F e

end AllThoseRamseyClasses.Lifts
