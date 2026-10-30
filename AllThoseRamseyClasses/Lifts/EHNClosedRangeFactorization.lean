import PartiteConstruction.Functional.WeakInvariant
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Exact EHN factorization through a CLOSED source-image range

The printed 2019 lift proof replaces a forbidden weak
homomorphism-embedding by its image in a target free amalgam.
This is justified ONLY when that image is a full native
function-closed target substructure. For set-valued partial
functions an arbitrary weak EHN map need not have closed range.

Under the explicit correct closed-range premise S=range(f),
however, the original weak EHN map factors as

  Source --surjective EHN--> Target.induce(S)
         --full embedding--> Target.

This is not merely the weak incidence-generated image quotient:
the middle structure is the ACTUAL full induced target with
complete function-value fibres. Each source irreducible test
still maps FULLY because its already verified target embedding
can be restricted to the closed target S.

Consequently a family genuinely closed under surjective
homomorphism-embedding images contains Target.induce(S), and the
latter is an injectively embedded forbidden source in Target.
No claim is made for an arbitrary nonclosed range. The separate
one-generator/unary-function theorem provides a useful valid
special case of this premise.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Restrict a genuine weak functional EHN map to ANY full native
function-closed target subset containing the entire map range.
The restricted map is still EHN on all full irreducible source
substructures, not just a weak homomorphism.

This is the essential valid source-image step: the target
closedness requirement is explicit and cannot be omitted. -/
theorem ehn_codRestrict_functionClosed
    {V W : Type v}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (S : Set W) (hS : B.IsClosed S)
    (hRange : ∀ x : V, f x ∈ S) :
    A.IsEHNHomomorphismEmbedding
      (B.induce S hS) (fun x => (⟨f x, hRange x⟩ : S)) := by
  constructor
  · constructor
    · intro Rel xs hrel
      change B.rel Rel (f ∘ xs)
      exact hf.1.1 Rel xs hrel
    · intro Fun xs y hy
      change f y ∈ B.func Fun (f ∘ xs)
      exact hf.1.2 Fun xs y hy
  · intro X E hIrred e
    obtain ⟨g, hg⟩ := hf.2 E hIrred e
    have hGRange : ∀ z : X, g z ∈ S := by
      intro z
      rw [hg z]
      exact hRange (e z)
    let gS : Structure.Embedding E (B.induce S hS) := {
      toFun := fun z => ⟨g z, hGRange z⟩
      injective := by
        intro a b hab
        apply g.injective
        exact congrArg Subtype.val hab
      map_rel_iff := by
        intro Rel xs
        exact g.map_rel_iff Rel xs
      map_func := by
        intro Fun xs
        ext y
        constructor
        · rintro ⟨z, hz, hzy⟩
          have hSourceValue : g z ∈ B.func Fun (g ∘ xs) := by
            rw [← g.map_func Fun xs]
            exact ⟨z, hz, rfl⟩
          have hEq : g z = y.1 :=
            congrArg Subtype.val hzy
          change y.1 ∈ B.func Fun (g ∘ xs)
          rw [← hEq]
          exact hSourceValue
        · intro hy
          have hImage : y.1 ∈ imageSet g (E.func Fun xs) := by
            rw [g.map_func Fun xs]
            exact hy
          obtain ⟨z, hz, hzy⟩ := hImage
          exact ⟨z, hz, Subtype.ext hzy⟩
    }
    refine ⟨gS, ?_⟩
    intro z
    apply Subtype.ext
    exact hg z

/-- The actual target-induced range factorization is SURJECTIVE
onto the induced source image, and its inclusion into Target is
a FULL native functional embedding. This repairs the structural
part of injectivization whenever the original range is closed. -/
theorem ehn_closedRange_surjectiveInducedFactor
    {V W : Type v}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hClosed : B.IsClosed (Set.range f)) :
    A.IsEHNHomomorphismEmbedding
      (B.induce (Set.range f) hClosed)
      (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) ∧
    Function.Surjective
      (fun x : V => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f)) := by
  refine ⟨ehn_codRestrict_functionClosed A B f hf
    (Set.range f) hClosed (fun x => ⟨x, rfl⟩), ?_⟩
  intro z
  obtain ⟨x, hx⟩ := z.2
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- A forbidden family closed under SURJECTIVE genuine EHN images
contains the full induced target structure on a CLOSED EHN range.

The latter embeds injectively into the original target by a full
functional embedding, giving a legitimate forbidden source with
NO image collisions. Unlike the printed unqualified image step,
closedness of range(f) is not hidden in a use of family closure. -/
theorem forbiddenFullInducedEHNImage_of_closedRange
    (F : ∀ {X : Type v}, Structure L X → Prop)
    (hImageClosed :
      ∀ {X Y : Type v}
        (Src : Structure L X) (Dst : Structure L Y)
        (q : X → Y),
        F Src →
        Src.IsEHNHomomorphismEmbedding Dst q →
        Function.Surjective q → F Dst)
    {V W : Type v}
    (A : Structure L V) (B : Structure L W)
    (hForbidden : F A)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hClosed : B.IsClosed (Set.range f)) :
    F (B.induce (Set.range f) hClosed) := by
  obtain ⟨hEHN, hSurj⟩ :=
    ehn_closedRange_surjectiveInducedFactor A B f hf hClosed
  exact hImageClosed A
    (B.induce (Set.range f) hClosed)
    (fun x => (⟨f x, ⟨x, rfl⟩⟩ : Set.range f))
    hForbidden hEHN hSurj

end AllThoseRamseyClasses.Lifts
