import PartiteConstruction.Structure.WeakHomomorphism

/-!
# Exact positive tuple-surjectivity of the functional weak image

The 2019 Section 3 homogenisation argument invokes closure of the
forbidden family under TUPLE-SURJECTIVE homomorphism-embedding images
to replace a noninjective forbidden witness before the minimal-support
flip induction.

The weak incidence-generated image has a canonical quotient map
surjective on its vertices AND on every positive relation/function
incidence, not merely on the domain of a function. We verify this
exactly, for arbitrary arities and set-valued function outputs.

WARNING: This does NOT identify a weak image with the FULL induced
structure on the image vertex set. The inclusion of a weak image
in its ambient target can have additional relations or function
values in the ambient structure, and need not be a full embedding.
Using the forbidden-family image-closure hypothesis to obtain an
injectively embedded forbidden source remains an additional
proof obligation.

For a language with separately *defined but empty-valued* partial
applications the original function-domain tokens also need to be
preserved explicitly. Ordinary set-valued membership encodes only
positive output incidences, so the present lemma is named
"PositiveIncidenceSurjective", not the paper's richer
tuple-surjective map without qualification.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {U V : Type v}

/-- Surjective on the vertices and on all positive relation/function
incidences, including the output of a function application. -/
def PositiveIncidenceSurjective
    (A : Structure L U) (B : Structure L V)
    (f : U → V) : Prop :=
  Function.Surjective f ∧
    (∀ R (xs : Fin (L.relArity R) → V),
      B.rel R xs →
      ∃ ys : Fin (L.relArity R) → U,
        A.rel R ys ∧ xs = f ∘ ys) ∧
    ∀ F (xs : Fin (L.funcArity F) → V) (y : V),
      y ∈ B.func F xs →
      ∃ (ys : Fin (L.funcArity F) → U) (z : U),
        z ∈ A.func F ys ∧ xs = f ∘ ys ∧ y = f z

/-- Positive-incidence surjectivity implies the paper's
tuple-surjectivity requirement for positive-valued function
domains: every target function input tuple with a genuine output
has an antecedent source input tuple with a genuine output. -/
theorem PositiveIncidenceSurjective.domains
    {A : Structure L U} {B : Structure L V}
    {f : U → V}
    (h : PositiveIncidenceSurjective A B f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (hdom : ∃ y, y ∈ B.func F xs) :
    ∃ ys : Fin (L.funcArity F) → U,
      (∃ z, z ∈ A.func F ys) ∧ xs = f ∘ ys := by
  obtain ⟨y, hy⟩ := hdom
  obtain ⟨ys, z, hz, hxs, _⟩ := h.2.2 F xs y hy
  exact ⟨ys, ⟨z, hz⟩, hxs⟩

/-- The incidence-generated weak image is by construction
surjective on all of its positive relation/function tuples. -/
theorem weakImage_quotient_positiveIncidenceSurjective
    (A : Structure L U) (B : Structure L V)
    (f : U → V) :
    PositiveIncidenceSurjective A
      (Structure.weakImage A B f)
      (Structure.weakImage.quotientMap (A := A) (B := B) (f := f)) := by
  let q : U → Set.range f :=
    Structure.weakImage.quotientMap (A := A) (B := B) (f := f)
  constructor
  · exact Structure.weakImage.quotientMap_surjective (f := f)
  constructor
  · intro R xs hx
    obtain ⟨ys, hys, hcoords⟩ := hx
    refine ⟨ys, hys, ?_⟩
    funext i
    exact hcoords i
  · intro F xs y hy
    obtain ⟨ys, z, hz, hcoords, hout⟩ := hy
    refine ⟨ys, z, hz, ?_, ?_⟩
    · funext i
      exact hcoords i
    · exact hout

/-- The same canonical image quotient is a weak homomorphism, as
verified upstream. Combining this with positive incidence
surjectivity still does NOT establish that its inclusion in the
target is a full embedding. -/
theorem weakImage_quotient_weak_and_positiveSurjective
    (A : Structure L U) (B : Structure L V)
    (f : U → V) :
    A.IsWeakHomomorphism (Structure.weakImage A B f)
      (Structure.weakImage.quotientMap (A := A) (B := B) (f := f)) ∧
    PositiveIncidenceSurjective A (Structure.weakImage A B f)
      (Structure.weakImage.quotientMap (A := A) (B := B) (f := f)) :=
  ⟨Structure.weakImage.quotientMap_weak (A := A) (B := B) (f := f),
    weakImage_quotient_positiveIncidenceSurjective A B f⟩

end AllThoseRamseyClasses.Lifts
