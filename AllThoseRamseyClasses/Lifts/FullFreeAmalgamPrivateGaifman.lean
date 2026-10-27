import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.GlobalFlipOuterContextOutside

/-!
# Exact Gaifman geometry of the retained private side of a full flip

Let Whole be a genuine native functional free amalgam of Left and
Right over Root. If a is private to Right (outside the embedded
root), every positive Gaifman tuple of Whole containing iRight(a)
must be a tuple of Right. Because the RIGHT embedding is FULL, not
merely a weak homomorphism, its complete relational graph reflects
that tuple. Thus adjacency of right-private vertices is EXACTLY
the old Gaifman adjacency.

For a right subset SR containing the entire shared root, the
complement of K = iLeft(Left) ∪ iRight(SR) is an actual copy of
Right\SR. Not just its source vertices, but its WHOLE induced
Gaifman adjacency and all finite paths agree with Right\SR.
This is a geometric strengthening of the exact complement-bijection
lemma and is needed to preserve external components when a B-only
source piece is replaced inside an outer piece.

No global or local injectivity of any FORBIDDEN weak target map is
used: all injections below are genuinely FULL source embeddings.
The result does not assert that a transported outer separator is
minimal or that incompatibility profiles coincide after the flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E}
variable {Right : Structure L F}
variable {Whole : Structure L W}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- A Gaifman edge in the whole full free amalgam touching one
RIGHT-private vertex is precisely an edge of the right-hand
source structure. The converse needs only the full embedding;
the private hypothesis is used to exclude a left-side tuple.

This applies to both original relations and whole set-valued
function incidence tuples (including arbitrary function arities). -/
theorem fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (a b : F)
    (haPrivate : a ∉ Set.range sR) :
    GaifmanAdjacent Whole.graph (iR a) (iR b) ↔
      GaifmanAdjacent Right.graph a b := by
  constructor
  · rintro ⟨hne, sym, xs, j, k, htuple, hj, hk⟩
    rcases functionalFreeAmalgam_graphTuple_side
        hFree sym xs htuple with hLeft | hRight
    · obtain ⟨aLeft, hLeftImage⟩ := hLeft j
      have hOverlap : iL aLeft = iR a :=
        hLeftImage.symm.trans hj
      obtain ⟨r, _, haRoot⟩ :=
        (hFree.overlap aLeft a).mp hOverlap
      exact False.elim (haPrivate ⟨r, haRoot.symm⟩)
    · classical
      choose tuple htupleImage using hRight
      have hTupleEq : xs = iR ∘ tuple := by
        funext t
        exact htupleImage t
      have hRightRel : Right.graph.rel sym tuple := by
        apply (iR.graph.map_rel_iff sym tuple).mp
        change Whole.graph.rel sym (iR ∘ tuple)
        rw [← hTupleEq]
        exact htuple
      have hja : tuple j = a :=
        iR.injective ((htupleImage j).symm.trans hj)
      have hkb : tuple k = b :=
        iR.injective ((htupleImage k).symm.trans hk)
      exact ⟨(fun hab => hne (congrArg iR hab)),
        sym, tuple, j, k, hRightRel, hja, hkb⟩
  · rintro ⟨hne, sym, xs, j, k, htuple, hj, hk⟩
    have hWholeRel : Whole.graph.rel sym (iR ∘ xs) :=
      (iR.graph.map_rel_iff sym xs).mpr htuple
    refine ⟨?_, sym, iR ∘ xs, j, k, hWholeRel, ?_, ?_⟩
    · intro hab
      exact hne (iR.injective hab)
    · exact congrArg iR hj
    · exact congrArg iR hk

/-- The actual source complement of the transported context is
in bijection with the unchanged right-hand vertex subset outside SR.
This uses exact free-amalgam cover and overlap, not a target quotient. -/
noncomputable def fullFreeAmalgam_rightOutsideContextEquiv
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set F)
    (hRootR : ∀ r : H, sR r ∈ SR) :
    {b : F // b ∉ SR} ≃
      {w : W // w ∉ (iL '' (Set.univ : Set E) ∪ iR '' SR)} := by
  classical
  let K : Set W := iL '' (Set.univ : Set E) ∪ iR '' SR
  let forward :
      {b : F // b ∉ SR} → {w : W // w ∉ K} :=
    fun b => ⟨iR b.1,
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hFree SR hRootR (iR b.1)).mpr ⟨b.1, b.2, rfl⟩⟩
  have hInj : Function.Injective forward := by
    intro a b hab
    apply Subtype.ext
    apply iR.injective
    exact congrArg Subtype.val hab
  have hSurj : Function.Surjective forward := by
    intro w
    obtain ⟨b, hb, hMap⟩ :=
      (fullFreeAmalgam_fullLeft_contextOutside_iff
        hFree SR hRootR w.1).mp w.2
    refine ⟨⟨b, hb⟩, ?_⟩
    exact Subtype.ext hMap
  exact Equiv.ofBijective forward ⟨hInj, hSurj⟩

/-- The right-outside-context bijection reflects every actual
Gaifman edge, because those vertices are private to the right
side. This is an exact graph isomorphism of outside subtypes. -/
theorem fullFreeAmalgam_rightOutsideContext_adj_iff
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (a b : {x : F // x ∉ SR}) :
    outsideAdjacency Whole.graph
      (iL '' (Set.univ : Set E) ∪ iR '' SR)
      ((fullFreeAmalgam_rightOutsideContextEquiv
        hFree SR hRootR) a)
      ((fullFreeAmalgam_rightOutsideContextEquiv
        hFree SR hRootR) b) ↔
    outsideAdjacency Right.graph SR a b := by
  have haPrivate : a.1 ∉ Set.range sR := by
    rintro ⟨r, hr⟩
    exact a.2 (hr ▸ hRootR r)
  exact fullFreeAmalgam_rightPrivate_gaifmanAdjacent_iff
    hFree a.1 b.1 haPrivate

/-- The preserved exterior is not merely a graph on the same
vertices: EVERY path avoiding the transported whole context is
exactly a path avoiding SR on the unchanged right-hand side.

This is the component-level locality invariant needed to
reconstruct the actual outer piece after a nested functional flip.
The preserved context itself need not yet be a minimal separator. -/
theorem fullFreeAmalgam_rightOutsideContext_reach_iff
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set F) (hRootR : ∀ r : H, sR r ∈ SR)
    (a b : {x : F // x ∉ SR}) :
    ReachOutside Whole.graph
      (iL '' (Set.univ : Set E) ∪ iR '' SR)
      ((fullFreeAmalgam_rightOutsideContextEquiv
        hFree SR hRootR) a)
      ((fullFreeAmalgam_rightOutsideContextEquiv
        hFree SR hRootR) b) ↔
    ReachOutside Right.graph SR a b := by
  let e := fullFreeAmalgam_rightOutsideContextEquiv
    hFree SR hRootR
  have hEdge (x y : {z : F // z ∉ SR}) :
      outsideAdjacency Whole.graph
        (iL '' (Set.univ : Set E) ∪ iR '' SR)
        (e x) (e y) ↔
      outsideAdjacency Right.graph SR x y :=
    fullFreeAmalgam_rightOutsideContext_adj_iff
      hFree SR hRootR x y
  constructor
  · intro hp
    have hAux :
        ∀ (x y : {z : W // z ∉
              (iL '' (Set.univ : Set E) ∪ iR '' SR)}),
          ReachOutside Whole.graph
            (iL '' (Set.univ : Set E) ∪ iR '' SR) x y →
          ReachOutside Right.graph SR (e.symm x) (e.symm y) := by
      intro x y h
      induction h with
      | refl => exact Relation.ReflTransGen.refl
      | @tail p q hpath hedge ih =>
          have hstep : outsideAdjacency Right.graph SR
              (e.symm p) (e.symm q) := by
            exact (hEdge (e.symm p) (e.symm q)).mp
              (by simpa only [e.apply_symm_apply] using hedge)
          exact ih.tail hstep
    simpa only [e.symm_apply_apply] using hAux (e a) (e b) hp
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail p q hpath hedge ih =>
        exact ih.tail ((hEdge p q).mpr hedge)

end AllThoseRamseyClasses.Lifts
