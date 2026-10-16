import AllThoseRamseyClasses.Lifts.ArbitraryFunctionalFreeFold

/-!
# Transport a FULL functional free amalgam along an isomorphism

A surjective full embedding transports an actual four-map functional
free-amalgam diagram to the target, preserving its exact intersection,
relation-tuple side localization and positive function incidences.

The inverse of the surjective full embedding is a WEAK functional
homomorphism: this uses equality of entire function-value sets
provided by the full embedding, NOT any surjectivity requirement on
the weak homomorphism-embeddings used for piece flips.

Together with the independent free-diagram uniqueness theorem this
identifies canonical functional gluing up to isomorphism with the
existential forbidden-source diagram predicate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {X Y : Type v}
variable {A : Structure L X} {B : Structure L Y}

/-- A full ONTO embedding has an inverse map that preserves
positive relation tuples and function-value incidences. -/
theorem surjectiveEmbedding_weakInverse
    (e : Structure.Embedding A B) (he : Function.Surjective e) :
    ∃ g : Y → X, B.IsWeakHomomorphism A g ∧
      (∀ y, e (g y) = y) ∧
      ∀ x, g (e x) = x := by
  classical
  let g : Y → X := fun y => Classical.choose (he y)
  have heg (y : Y) : e (g y) = y :=
    Classical.choose_spec (he y)
  have hge (x : X) : g (e x) = x :=
    e.injective (heg (e x))
  have hweak : B.IsWeakHomomorphism A g := by
    constructor
    · intro R ys hys
      have hargs : e ∘ (g ∘ ys) = ys := by
        funext i
        exact heg (ys i)
      have hrel : B.rel R (e ∘ (g ∘ ys)) := by
        rw [hargs]
        exact hys
      exact (e.map_rel_iff R (g ∘ ys)).mp hrel
    · intro F ys y hy
      have hargs : e ∘ (g ∘ ys) = ys := by
        funext i
        exact heg (ys i)
      have hval : y ∈ B.func F (e ∘ (g ∘ ys)) := by
        rw [hargs]
        exact hy
      have hmem : y ∈ imageSet e (A.func F (g ∘ ys)) := by
        rw [e.map_func F (g ∘ ys)]
        exact hval
      rcases hmem with ⟨z, hz, hze⟩
      have hzg : z = g y := e.injective (hze.trans (heg y).symm)
      exact hzg ▸ hz
  exact ⟨g, hweak, heg, hge⟩

/-- Transport a full functional free-amalgam diagram through
any surjective full embedding of its whole source into the target.
In particular, the free diagram survives arbitrary renaming of its
whole carrier, even if the forbidden family is not assumed to be
closed under renaming as a primitive axiom. -/
theorem freeAmalgamDiagram_transport_surjective
    {H E F : Type v}
    {Root : Structure L H}
    {Left : Structure L E} {Right : Structure L F}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left A}
    {iR : Structure.Embedding Right A}
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (e : Structure.Embedding A B)
    (he : Function.Surjective e) :
    Structure.IsFreeAmalgam sL sR (e.comp iL) (e.comp iR) := by
  classical
  obtain ⟨g, hg, heg, hge⟩ := surjectiveEmbedding_weakInverse e he
  have heWeak : A.IsWeakHomomorphism B e := e.isWeakHomomorphism
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro y
    obtain ⟨x, hx⟩ := he y
    rcases hfree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, hx.symm.trans (congrArg e ha)⟩
    · exact Or.inr ⟨b, hx.symm.trans (congrArg e hb)⟩
  · intro a b
    constructor
    · intro hab
      exact (hfree.overlap a b).mp (e.injective hab)
    · intro hab
      exact congrArg e ((hfree.overlap a b).mpr hab)
  · intro R ys
    constructor
    · intro hy
      have hsrc : A.rel R (g ∘ ys) := hg.1 R ys hy
      rcases (hfree.rel_iff R (g ∘ ys)).mp hsrc with
        ⟨as, has, hargs⟩ | ⟨bs, hbs, hargs⟩
      · refine Or.inl ⟨as, has, ?_⟩
        calc
          ys = e ∘ (g ∘ ys) := by
            funext i
            exact (heg (ys i)).symm
          _ = e ∘ (iL ∘ as) := congrArg (fun t => e ∘ t) hargs
          _ = (e.comp iL) ∘ as := rfl
      · refine Or.inr ⟨bs, hbs, ?_⟩
        calc
          ys = e ∘ (g ∘ ys) := by
            funext i
            exact (heg (ys i)).symm
          _ = e ∘ (iR ∘ bs) := congrArg (fun t => e ∘ t) hargs
          _ = (e.comp iR) ∘ bs := rfl
    · rintro (⟨as, has, hargs⟩ | ⟨bs, hbs, hargs⟩)
      · rw [hargs]
        exact heWeak.1 R (iL ∘ as)
          ((hfree.rel_iff R (iL ∘ as)).mpr
            (Or.inl ⟨as, has, rfl⟩))
      · rw [hargs]
        exact heWeak.1 R (iR ∘ bs)
          ((hfree.rel_iff R (iR ∘ bs)).mpr
            (Or.inr ⟨bs, hbs, rfl⟩))
  · intro F ys y
    constructor
    · intro hy
      have hsrc : g y ∈ A.func F (g ∘ ys) := hg.2 F ys y hy
      rcases (hfree.func_iff F (g ∘ ys) (g y)).mp hsrc with
        ⟨as, a, ha, hargs, hout⟩ | ⟨bs, b, hb, hargs, hout⟩
      · refine Or.inl ⟨as, a, ha, ?_, ?_⟩
        · calc
            ys = e ∘ (g ∘ ys) := by
              funext i
              exact (heg (ys i)).symm
            _ = e ∘ (iL ∘ as) := congrArg (fun t => e ∘ t) hargs
            _ = (e.comp iL) ∘ as := rfl
        · calc
            y = e (g y) := (heg y).symm
            _ = e (iL a) := congrArg e hout
            _ = (e.comp iL) a := rfl
      · refine Or.inr ⟨bs, b, hb, ?_, ?_⟩
        · calc
            ys = e ∘ (g ∘ ys) := by
              funext i
              exact (heg (ys i)).symm
            _ = e ∘ (iR ∘ bs) := congrArg (fun t => e ∘ t) hargs
            _ = (e.comp iR) ∘ bs := rfl
        · calc
            y = e (g y) := (heg y).symm
            _ = e (iR b) := congrArg e hout
            _ = (e.comp iR) b := rfl
    · rintro (⟨as, a, ha, hargs, hout⟩ |
              ⟨bs, b, hb, hargs, hout⟩)
      · rw [hargs, hout]
        exact heWeak.2 F (iL ∘ as) (iL a)
          ((hfree.func_iff F (iL ∘ as) (iL a)).mpr
            (Or.inl ⟨as, a, ha, rfl, rfl⟩))
      · rw [hargs, hout]
        exact heWeak.2 F (iR ∘ bs) (iR b)
          ((hfree.func_iff F (iR ∘ bs) (iR b)).mpr
            (Or.inr ⟨bs, b, hb, rfl, rfl⟩))

end AllThoseRamseyClasses.Lifts
