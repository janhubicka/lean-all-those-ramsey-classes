import AllThoseRamseyClasses.Lifts.EHNBadTestFreeSideLocalization

/-!
# Track D: identify the precise full-reflection failure of a side-local weak test

A generic WEAK map of genuine native functional structures can fail
to be a FULL embedding for three logically exhaustive reasons:

1. it COLLAPSES distinct source vertices;
2. it does not reflect some positive RELATION tuple;
3. the target carries an additional FUNCTION VALUE at an image
   input that is not a source-value image.

The forward preservation requirements of a weak homomorphism
already rule out all other defects, including losses of source
relations or function incidences.

This module proves the trichotomy from the *negation* of the
existence of a coordinate-prescribed full embedding, then applies
it to the original finite forbidden-source bad-test witness
localized by the genuine FULL free-amalgam geometry.

The result is deliberately narrower than a claimed repair of
2019 Section 3. In the maximal common-lift setting one must
eliminate the relevant specific defect using canonical
root/boundary data, or work around it by a collision-tolerant
flip. The verified two-point F-free side counterexample shows
that bare forbidden-freeness does not remove target-only tuples.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An explicitly checkable failure of FULL reflection for a
native weak map: a collision, an additional target relation,
or an additional target function value.

The last alternative uses the COMPLETE target function fibre
and is stronger than just comparing defined/undefined domains. -/
def WeakMapFullReflectionDefect
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W) : Prop :=
  (∃ x y : V, x ≠ y ∧ f x = f y) ∨
  (∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
    B.rel R (f ∘ xs) ∧ ¬ A.rel R xs) ∨
  (∃ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
      (z : W),
    z ∈ B.func F (f ∘ xs) ∧
      z ∉ imageSet f (A.func F xs))

/-- Under positive weak homomorphism preservation, failure of
a full embedding with the SAME vertex coordinates supplies
a genuine native collision / extra-relation / extra-fibre
witness. No finiteness, function arity, or irreducibility
assumptions are needed. -/
theorem weakMap_noFullEmbedding_exposesReflectionDefect
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsWeakHomomorphism B f)
    (hNoFull : ¬ ∃ e : Structure.Embedding A B,
      ∀ x : V, e x = f x) :
    WeakMapFullReflectionDefect A B f := by
  classical
  by_contra hNoDefect
  have hInj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact hNoDefect (Or.inl ⟨x, y, hne, hxy⟩)
  let e : Structure.Embedding A B := {
    toFun := f
    injective := hInj
    map_rel_iff := by
      intro R xs
      constructor
      · intro hTarget
        by_contra hMissing
        exact hNoDefect
          (Or.inr (Or.inl ⟨R, xs, hTarget, hMissing⟩))
      · exact hf.1 R xs
    map_func := by
      intro F xs
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hf.2 F xs y hy
      · intro hTarget
        by_contra hMissing
        exact hNoDefect
          (Or.inr (Or.inr ⟨F, xs, z, hTarget, hMissing⟩))
  }
  exact hNoFull ⟨e, fun _ => rfl⟩

/-- Once a weak map is INJECTIVE on its source vertices,
the only possible failure of full reflection is a target-only
old relation tuple or a target-only function-fibre value. -/
def WeakMapFullReflectionSurplus
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W) : Prop :=
  (∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
    B.rel R (f ∘ xs) ∧ ¬ A.rel R xs) ∨
  (∃ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V)
      (z : W),
    z ∈ B.func F (f ∘ xs) ∧
      z ∉ imageSet f (A.func F xs))

/-- For injective weak maps, the collision branch of the
generic full-reflection trichotomy is impossible. -/
theorem injectiveWeakMap_noFullEmbedding_exposesSurplus
    {V W : Type} (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsWeakHomomorphism B f)
    (hInjective : Function.Injective f)
    (hNoFull : ¬ ∃ e : Structure.Embedding A B,
      ∀ x : V, e x = f x) :
    WeakMapFullReflectionSurplus A B f := by
  rcases weakMap_noFullEmbedding_exposesReflectionDefect
      A B f hf hNoFull with hCollision | hRelation | hFunction
  · obtain ⟨x, y, hne, hxy⟩ := hCollision
    exact False.elim (hne (hInjective hxy))
  · exact Or.inl hRelation
  · exact Or.inr hFunction

/-- For an actual bad irreducible forbidden-copy test in the
generated weak quotient of a forbidden EHN witness into a
genuine full native free amalgam, the defect is SIDE-LOCAL.

This retains:
- the specific forbidden full quotient-copy P;
- its actual irreducible FULL test E and full inclusion h;
- the impossibility of a source test-lift with the same
  quotient coordinates;
- and the actual weak side-map with exactly the prescribed
  target coordinates.

The full embeddings E ↪ P ↪ Q and the injective subtype inclusion
Q ↪ Target make the prescribed target coordinate map on E
INJECTIVE, even when the ORIGINAL forbidden-source witness
is noninjective. Any side factorization has the same images and
is therefore injective too.

Hence the side-map has only TWO possible full-reflection defects:
an extra target relation tuple, or an extra target function-fibre
value. The collision branch is impossible for this specific
quotient-derived test. The whole quotient is never treated as full. -/
theorem badForbiddenWeakImageTest_hasSideReflectionDefect
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UX UA UB UT : Type}
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (w : ForbiddenEHNWitness F Target)
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
    ∃ (Z : Type) (P : Structure L Z),
      F P ∧
      ∃ (e : Structure.Embedding P
        (Structure.weakImage w.source Target w.toTarget))
        (U : Type) (E : Structure L U),
        E.Irreducible ∧
        ∃ (h : Structure.Embedding E P),
          (¬ ∃ k : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∃ g : U → UA,
             E.IsWeakHomomorphism Left g ∧
             (∀ x : U, jL (g x) = (e (h x)).1) ∧
             WeakMapFullReflectionSurplus E Left g) ∨
           (∃ g : U → UB,
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             WeakMapFullReflectionSurplus E Right g)) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoTarget, hNoLift, hSide⟩ :=
    badForbiddenWeakImageTest_hasSideInternalReflectionFailure
      F Root Left Right Target sL sR jL jR hFree w hBad
  let Q : Structure L (Set.range w.toTarget) :=
    Structure.weakImage w.source Target w.toTarget
  have hWeakQ : E.IsWeakHomomorphism Q (e ∘ h) :=
    (e.comp h).isWeakHomomorphism
  have hWeakTarget : E.IsWeakHomomorphism Target
      (fun x => (e (h x)).1) :=
    (Structure.weakImage.inclusion_weak w.homEmbedding.1).comp
      hWeakQ
  have hPrescribedInjective :
      Function.Injective (fun x : U => (e (h x)).1) := by
    intro x y heq
    apply h.injective
    apply e.injective
    exact Subtype.ext heq
  refine ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, ?_⟩
  rcases hSide with ⟨hL, hNoL⟩ | ⟨hR, hNoR⟩
  · left
    obtain ⟨g, hgWeak, hgCoords⟩ :=
      weakHomomorphism_factor_fullSide hWeakTarget jL hL
    have hNoEmbed : ¬ ∃ k : Structure.Embedding E Left,
        ∀ x : U, k x = g x := by
      rintro ⟨k, hk⟩
      apply hNoL
      exact ⟨k, fun x =>
        (congrArg jL (hk x)).trans (hgCoords x)⟩
    have hgInjective : Function.Injective g := by
      intro x y heq
      apply hPrescribedInjective
      calc
        (e (h x)).1 = jL (g x) := (hgCoords x).symm
        _ = jL (g y) := congrArg jL heq
        _ = (e (h y)).1 := hgCoords y
    exact ⟨g, hgWeak, hgCoords,
      injectiveWeakMap_noFullEmbedding_exposesSurplus
        E Left g hgWeak hgInjective hNoEmbed⟩
  · right
    obtain ⟨g, hgWeak, hgCoords⟩ :=
      weakHomomorphism_factor_fullSide hWeakTarget jR hR
    have hNoEmbed : ¬ ∃ k : Structure.Embedding E Right,
        ∀ x : U, k x = g x := by
      rintro ⟨k, hk⟩
      apply hNoR
      exact ⟨k, fun x =>
        (congrArg jR (hk x)).trans (hgCoords x)⟩
    have hgInjective : Function.Injective g := by
      intro x y heq
      apply hPrescribedInjective
      calc
        (e (h x)).1 = jR (g x) := (hgCoords x).symm
        _ = jR (g y) := congrArg jR heq
        _ = (e (h y)).1 := hgCoords y
    exact ⟨g, hgWeak, hgCoords,
      injectiveWeakMap_noFullEmbedding_exposesSurplus
        E Right g hgWeak hgInjective hNoEmbed⟩

end AllThoseRamseyClasses.Lifts
