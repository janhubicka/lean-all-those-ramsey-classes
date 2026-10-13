import AllThoseRamseyClasses.Published.NativeTwoActivePrivate2019

/-!
# Every genuinely nonlocal two-copy native relation tuple lies in the CORE

The explicit exact source tuple-localization hypothesis of the
CI-green native two-copy completion lemma #172 is NOT automatic:
the coordinatewise native power can carry relations between
exclusive vertices in two transverse line images (CI-green
counterexample #170).

There is nevertheless a useful completely general native
structural fact, requiring NO closure, HJ parameter disjointness,
positive-map injectivity or restrictions on relational arity:

If an ACTUAL attachment relation tuple has all its vertices
inside the union of two selected attached Old-copy ranges,
but the tuple is not wholly within EITHER range, then EVERY
vertex of the tuple must be in the central power CORE.

Proof: an attachment relation tuple containing a private exterior
vertex has to arise from the UNIQUE attached copy indexed by that
vertex. If that copy is one of the two selected ranges then all
tuple entries belong to it, contradicting nonlocality. If it is
a THIRD copy, its private vertex belongs to neither selected
copy, contradicting vertex coverage. Thus no private exterior
entry occurs, so every entry is a core vertex.

The source corollary transports this exactly through an arbitrary
POSITIVE (possibly noninjective) map of the ORIGINAL weak test.

This identifies where genuine nonlocality can occur: it is a
PURE-CORE crossing, not a relation between the two different
private exterior fibres. It does NOT make the tuple local,
construct compatible K-completions over that core, or prove the
full corrected 2019 Lemma 2.30 / Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.Attachment

universe u v
variable {L : RelLanguage.{u}}

/-- In an ACTUAL native attachment, any relation tuple covered
pointwise by the images of two attached old copies but not wholly
in either image lies ENTIRELY in the coordinate power core.

The selected copy indices may be arbitrary. There is no HJ
transversality, U-closure or injectivity hypothesis. -/
theorem native2019_nonlocal_two_copy_tuple_is_pure_core
    {V W I : Type v}
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (i j : I) (R : L.Symbol)
    (z : Fin (L.arity R) →
      Vertex Support (W := W) (I := I))
    (hz : (attach Old Support Core maps).rel R z)
    (hCovered : ∀ k,
      InCopy Old Support Core maps i (z k) ∨
      InCopy Old Support Core maps j (z k))
    (hNonI : ¬ ∀ k, InCopy Old Support Core maps i (z k))
    (hNonJ : ¬ ∀ k, InCopy Old Support Core maps j (z k)) :
    ∀ k, ∃ w : W, z k = Sum.inl w := by
  classical
  intro k
  cases hv : z k with
  | inl w =>
      exact ⟨w, rfl⟩
  | inr pair =>
      have hAll : ∀ l,
          InCopy Old Support Core maps pair.1 (z l) := by
        obtain ⟨ys, _, heq⟩ :=
          relation_eq_copy_of_contains_outside
            (B := Old) (S := Support) (D := Core) (f := maps)
            hz k pair.1 pair.2 hv
        intro l
        exact ⟨ys l, congrFun heq l⟩
      by_cases hi : pair.1 = i
      · subst i
        exact False.elim (hNonI hAll)
      by_cases hj : pair.1 = j
      · subst j
        exact False.elim (hNonJ hAll)
      have hPrivate : OutsideAt (W := W) (I := I)
          Support pair.1 (z k) := ⟨pair.2, hv⟩
      rcases hCovered k with hI | hJ
      · obtain ⟨x, hx⟩ := hI
        have hNot :
            ¬ OutsideAt (W := W) (I := I)
              Support pair.1
              (copyMap Old Support Core maps i x) :=
          copyMap_not_outside_of_ne
            (B := Old) (S := Support) (D := Core) (f := maps)
            (i := pair.1) i (Ne.symm hi) x
        exact False.elim (hNot (hx ▸ hPrivate))
      · obtain ⟨y, hy⟩ := hJ
        have hNot :
            ¬ OutsideAt (W := W) (I := I)
              Support pair.1
              (copyMap Old Support Core maps j y) :=
          copyMap_not_outside_of_ne
            (B := Old) (S := Support) (D := Core) (f := maps)
            (i := pair.1) j (Ne.symm hj) y
        exact False.elim (hNot (hy ▸ hPrivate))

/-- The same statement on the EXACT ORIGINAL weak source:
under a merely POSITIVE source map, if every tested tuple entry
belongs to one of two genuine native attached copies but the
tuple itself lies wholly in neither, ALL its projected entries
are core vertices. No source image or weak hull is substituted. -/
theorem native2019_nonlocal_positive_source_tuple_is_pure_core
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (i j : I) (R : L.Symbol)
    (xs : Fin (L.arity R) → U)
    (hxs : Source.rel R xs)
    (hCovered : ∀ k,
      InCopy Old Support Core maps i (p (xs k)) ∨
      InCopy Old Support Core maps j (p (xs k)))
    (hNonI : ¬ ∀ k, InCopy Old Support Core maps i (p (xs k)))
    (hNonJ : ¬ ∀ k, InCopy Old Support Core maps j (p (xs k))) :
    ∀ k, ∃ w : W, p (xs k) = Sum.inl w :=
  native2019_nonlocal_two_copy_tuple_is_pure_core
    Old Support Core maps i j R (p ∘ xs)
    (hp R xs hxs) hCovered hNonI hNonJ


/-- To verify the original exact two-copy SOURCE tuple-localization,
it suffices to check tuples whose ENTIRE native image is in the
power core. Every other native relation tuple is automatically
local to one of the two attached copy images, provided ALL source
vertices are covered by those two images.

This is a useful strictly more TARGETED premise for the existing
true two-copy K-completion theorem. It does not presume core
tuples localize automatically. -/
theorem native2019_two_copy_source_tuples_local_of_core_tuples_local
    {U V W I : Type v}
    (Source : RelStructure L U)
    (Old : RelStructure L V)
    (Support : Set V)
    (Core : RelStructure L W)
    (maps : I → Embedding (Old.induce Support) Core)
    (p : U → Vertex Support (W := W) (I := I))
    (hp : Source.IsHomomorphism (attach Old Support Core maps) p)
    (i j : I)
    (hVertices : ∀ x : U,
      InCopy Old Support Core maps i (p x) ∨
      InCopy Old Support Core maps j (p x))
    (hCoreTuples : ∀ R (xs : Fin (L.arity R) → U),
      Source.rel R xs →
      (∀ k, ∃ w : W, p (xs k) = Sum.inl w) →
      (∀ k, InCopy Old Support Core maps i (p (xs k))) ∨
      (∀ k, InCopy Old Support Core maps j (p (xs k)))) :
    ∀ R (xs : Fin (L.arity R) → U),
      Source.rel R xs →
      (∀ k, InCopy Old Support Core maps i (p (xs k))) ∨
      (∀ k, InCopy Old Support Core maps j (p (xs k))) := by
  classical
  intro R xs hxs
  by_cases hLocal :
      (∀ k, InCopy Old Support Core maps i (p (xs k))) ∨
      (∀ k, InCopy Old Support Core maps j (p (xs k)))
  · exact hLocal
  · have hNotI :
        ¬ ∀ k, InCopy Old Support Core maps i (p (xs k)) := by
      intro h
      exact hLocal (.inl h)
    have hNotJ :
        ¬ ∀ k, InCopy Old Support Core maps j (p (xs k)) := by
      intro h
      exact hLocal (.inr h)
    have hCovered :
        ∀ k, InCopy Old Support Core maps i (p (xs k)) ∨
          InCopy Old Support Core maps j (p (xs k)) :=
      fun k => hVertices (xs k)
    have hCore :
        ∀ k, ∃ w : W, p (xs k) = Sum.inl w :=
      native2019_nonlocal_positive_source_tuple_is_pure_core
        Source Old Support Core maps p hp
        i j R xs hxs hCovered hNotI hNotJ
    exact hCoreTuples R xs hxs hCore


end AllThoseRamseyClasses.Published
