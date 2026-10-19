import AllThoseRamseyClasses.Lifts.MaximalGlobalLiftAlong

/-!
# Actual induced traces of the original global functional-piece lift

The 2019 canonical global lift does not commute with restriction of
the old shadow: a piece may be realized in an allowed witness outside
the smaller old substructure. The appropriate hereditary objects
therefore use the FULL induced relation trace of a larger witness
on a designated fully embedded root. All native relation and
partial/set-valued function fibres remain EXACTLY those of the
designated old root.

This module constructs that trace and its full embedding into the
canonical lift of its witness. When the witness is maximal along
the designated root, every further allowed full extension preserves
the FULL trace: new piece witnesses cannot change its predicates.

The construction is valid for an arbitrary forbidden family. Finite
existence of maximizing witnesses follows separately from regularity
and finite-profile maximization. Nothing in this module asserts the
still-open full Section 3 strong-amalgamation or Ramsey theorem.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Maximality along a root is inherited by EVERY further full
restriction of that root. No finiteness or strong-amalgamation
hypothesis is needed. -/
theorem GlobalCanonicalMaximalAlong.restrict_root
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UY UA : Type}
    {X : Structure L UX} {Y : Structure L UY}
    {A : Structure L UA}
    (iA : Structure.Embedding Y A)
    (small : Structure.Embedding X Y)
    (hMax : GlobalCanonicalMaximalAlong F K iA) :
    GlobalCanonicalMaximalAlong F K (iA.comp small) := by
  intro UC C hC e s xs
  have h := hMax C hC e s (small ∘ xs)
  simpa only [Function.comp_assoc] using h

/-- The FULL induced original global canonical lift on X as SEEN
inside a larger old-language witness A. In general this is not
equal to the canonical lift of X alone. -/
noncomputable def globalCanonicalInducedTrace
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Structure (globalFunctionalPieceLanguage F) UX :=
  functionalWithExtraBig L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    X
    (fun s xs => (globalFunctionalCanonicalLift F A).rel
      (.inr s) (iA ∘ xs))

/-- Tracing the lifted relations changes NONE of the original
functional shadow, including all function values and domains. -/
@[simp] theorem globalCanonicalInducedTrace_shadow
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    functionalShadowBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (globalCanonicalInducedTrace F iA) = X :=
  functionalShadowBig_withExtra L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F) X _

/-- The true induced trace embeds FULLY into the original canonical
lift of its witness. The underlying map is exactly iA, and the
new relations are reflected by their definition, rather than by a
false reflection claim about arbitrary old-language embeddings. -/
noncomputable def globalCanonicalInducedTrace_into_witness
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) :
    Structure.Embedding
      (globalCanonicalInducedTrace F iA)
      (globalFunctionalCanonicalLift F A) := by
  apply functionalWithExtraBigEmbedding L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (fun s xs =>
      (globalFunctionalCanonicalLift F A).rel
        (.inr s) (iA ∘ xs))
    (functionalCanonicalExtraBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (globalFunctionalPieceRepresentatives F) A)
    iA
  intro s xs
  exact Iff.rfl

/-- The full trace inclusion has literally the same vertex map
as the supplied original old functional embedding. -/
@[simp] theorem globalCanonicalInducedTrace_into_witness_apply
    (F : ∀ {W : Type}, Structure L W → Prop)
    {UX UA : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A) (x : UX) :
    globalCanonicalInducedTrace_into_witness F iA x = iA x :=
  rfl

/-- A maximal witness preserves the FULL induced trace on X
through any allowed extension. In particular, the trace is still
a full expansion of X with its original complete function fibres.
No restriction is imposed on new witnesses elsewhere in C. -/
noncomputable def globalCanonicalInducedTrace_into_allowed_extension
    (F K : ∀ {W : Type}, Structure L W → Prop)
    {UX UA UC : Type}
    {X : Structure L UX} {A : Structure L UA}
    (iA : Structure.Embedding X A)
    (hMax : GlobalCanonicalMaximalAlong F K iA)
    (C : Structure L UC) (hC : K C)
    (e : Structure.Embedding A C) :
    Structure.Embedding
      (globalCanonicalInducedTrace F iA)
      (globalFunctionalCanonicalLift F C) := by
  apply functionalWithExtraBigEmbedding L
    (GlobalFunctionalPieceSymbol F)
    (globalFunctionalPieceArity F)
    (fun s xs =>
      (globalFunctionalCanonicalLift F A).rel
        (.inr s) (iA ∘ xs))
    (functionalCanonicalExtraBig L
      (GlobalFunctionalPieceSymbol F)
      (globalFunctionalPieceArity F)
      (globalFunctionalPieceRepresentatives F) C)
    (e.comp iA)
  intro s xs
  exact hMax C hC e s xs

end AllThoseRamseyClasses.Lifts
