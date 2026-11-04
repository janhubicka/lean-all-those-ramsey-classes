import AllThoseRamseyClasses.Lifts.EHNBadTestFreeSideLocalization
import AllThoseRamseyClasses.Lifts.EHNFiveCycleImageClosedFamily
import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance
import Mathlib.Tactic

/-!
# Track D: forbidden-free side does not imply full reflection of weak irreducible tests

A tempting repair to the original lift injectivization gap is to
observe that a bad irreducible test maps weakly into ONE side of
the genuine full free amalgam, then claim that the side's
membership in Forb_EHN(F) makes that map FULL or EHN.

That implication is FALSE, even for the explicitly verified
finite, connected, printed-image-closed family F_C5 of
C5 tuple-surjective homomorphism-embedding images.

Use the same old language:
  E : symmetric loopless binary relation
  T : independent ternary relation.
Let Side be the two-vertex complete E graph with extra
T(0,1,0). It is forbidden-free for F_C5, because a C5 map
to a two-point E graph would be a proper 2-colouring of an
odd cycle. Let Test be the two-vertex E edge with EMPTY T.

Test is irreducible, and the identity Test → Side is a
positive/weak homomorphism. But no full embedding can agree
with this identity: its ternary relation would have to
reflect T(0,1,0) back into Test, where it is absent.
Hence the weak identity is NOT EHN.

This does NOT refute the maximal-lift theorem or the exact
source-generated-quotient geometry. It shows that a proposed
shortcut replacing the missing local reflection theorem by
bare Forb_EHN(F)-freeness of a side cannot work. The original
specific maximal-lift compatibility/profiles remain essential.
-/

namespace AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Lifts.RootCollisionFiveCycle

/-- Irreducible binary edge with no ternary tuples. -/
abbrev twoPointEdgeTest : Structure language (Fin 2) where
  rel
    | false, xs => xs 0 ≠ xs 1
    | true, _ => False
  func f := nomatch f

/-- Forbidden-free side with the SAME edge and a new old-language
ternary tuple. The tuple has a repeated endpoint and therefore
cannot itself create a forbidden C5 proper 2-colouring. -/
abbrev twoPointEdgeWithExtraT : Structure language (Fin 2) where
  rel
    | false, xs => xs 0 ≠ xs 1
    | true, xs => xs 0 = 0 ∧ xs 1 = 1 ∧ xs 2 = 0
  func f := nomatch f

/-- No homomorphism of the five-cycle into the loopless
two-vertex E graph: a C5 cannot be properly 2-coloured. -/
theorem cycle5_no_properTwoColouring :
    ∀ c : Fin 5 → Fin 2,
      ¬ (∀ a b : Fin 5,
          cycle5Edge a b → c a ≠ c b) := by
  decide +kernel

/-- The two-point target with the extra ternary tuple is
genuinely forbidden-free for the ENTIRE image-closed family.
We show no forbidden native EHN map exists, not merely
that the five-cycle is not a full embedded substructure. -/
theorem twoPointSide_avoids_fiveCycleImageFamily :
    AvoidsGlobalFunctionalEHN fiveCycleImageFamily
      twoPointEdgeWithExtraT := by
  intro U P _ hP g hg
  obtain ⟨f, _, hfHE, _⟩ := hP
  have hProper :
      ∀ a b : Fin 5, cycle5Edge a b →
        g (f a) ≠ g (f b) := by
    intro a b hab
    let xs : Fin (language.relArity false) → Fin 5 :=
      fun i => if i.val = 0 then a else b
    have hOld : cycle5.rel false xs := by
      change cycle5Edge (xs 0) (xs 1)
      simpa [xs] using hab
    have hInP : P.rel false (f ∘ xs) :=
      hfHE.1.1 false xs hOld
    have hTarget :
        twoPointEdgeWithExtraT.rel false (g ∘ (f ∘ xs)) :=
      hg.1.1 false (f ∘ xs) hInP
    change g (f a) ≠ g (f b) at hTarget
    exact hTarget
  exact (cycle5_no_properTwoColouring (fun a => g (f a)))
    hProper

private def testEdge0 : Fin (language.graph.arity (.inl false)) :=
  ⟨0, by decide⟩

private def testEdge1 : Fin (language.graph.arity (.inl false)) :=
  ⟨1, by decide⟩

private theorem testEdge1_ne_testEdge0 : testEdge1 ≠ testEdge0 := by decide

/-- The test structure is genuinely irreducible: its only two
distinct vertices appear together in a positive source E tuple. -/
theorem twoPointEdgeTest_irreducible :
    twoPointEdgeTest.Irreducible := by
  apply irreducible_of_graph_irreducible
  intro x y hxy
  let xs : Fin (language.graph.arity (.inl false)) → Fin 2 :=
    fun i => if i = testEdge0 then x else y
  have hx : xs testEdge0 = x := by simp [xs]
  have hy : xs testEdge1 = y := by
    change (if testEdge1 = testEdge0 then x else y) = y
    exact if_neg testEdge1_ne_testEdge0
  have hed : twoPointEdgeTest.graph.rel (.inl false) xs := by
    change xs testEdge0 ≠ xs testEdge1
    rw [hx, hy]
    exact hxy
  exact ⟨.inl false, xs, testEdge0, testEdge1, hed, hx, hy⟩

/-- The identity from the irreducible source to the forbidden-free
side preserves ALL positive original relations and function
incidences. It is a bona fide native weak homomorphism. -/
theorem twoPointTest_weak_into_forbiddenFreeSide :
    twoPointEdgeTest.IsWeakHomomorphism
      twoPointEdgeWithExtraT (id : Fin 2 → Fin 2) := by
  constructor
  · intro R xs hRel
    cases R with
    | false =>
      exact hRel
    | true =>
      exact False.elim hRel
  · intro F
    exact Empty.elim F

/-- The identity weak map cannot be represented by a FULL
embedding. The added ternary tuple in the forbidden-free side
would have to reflect back to the source test, which has no T. -/
theorem twoPointTest_noFullEmbedding_atIdentity :
    ¬ ∃ e : Structure.Embedding
        twoPointEdgeTest twoPointEdgeWithExtraT,
        ∀ x : Fin 2, e x = x := by
  rintro ⟨e, hId⟩
  let xs : Fin 3 → Fin 2 := ![0, 1, 0]
  have hExtra : twoPointEdgeWithExtraT.rel true xs := by
    decide
  have hTarget :
      twoPointEdgeWithExtraT.rel true (e ∘ xs) := by
    have hArgs : e ∘ xs = xs := by
      funext i
      exact hId (xs i)
    rw [hArgs]
    exact hExtra
  have hSource : twoPointEdgeTest.rel true xs :=
    (e.map_rel_iff true xs).mp hTarget
  exact hSource

/-- A genuine irreducible source has a weak map to an actual
forbidden-free side, but this map is NOT EHN. Otherwise the
irreducible-test clause applied to the whole Test would produce
exactly the forbidden full identity embedding. -/
theorem twoPointTest_weak_notEHN_forbiddenFreeSide :
    twoPointEdgeTest.IsWeakHomomorphism
        twoPointEdgeWithExtraT (id : Fin 2 → Fin 2) ∧
      ¬ twoPointEdgeTest.IsEHNHomomorphismEmbedding
        twoPointEdgeWithExtraT (id : Fin 2 → Fin 2) := by
  refine ⟨twoPointTest_weak_into_forbiddenFreeSide, ?_⟩
  intro hEHN
  obtain ⟨e, he⟩ :=
    hEHN.2 twoPointEdgeTest twoPointEdgeTest_irreducible
      (Structure.Embedding.id twoPointEdgeTest)
  exact twoPointTest_noFullEmbedding_atIdentity ⟨e, he⟩

/-- Formal conjunction: even for a finite, connected and
printed-image-closed forbidden family, a forbidden-free full
side can carry a merely weak map of an irreducible test
which does not extend to an EHN map with the same coordinates.

This is a COUNTEREXAMPLE to a potential shortcut, not to the
2019 maximal-lift strong-amalgamation theorem. -/
theorem fiveCycleImageFamily_forbiddenFreeSide_notFullWeakTest :
    HasTupleSurjectiveForbiddenImageClosure
        (L := language) fiveCycleImageFamily ∧
      GlobalForbiddenSourcesConnectedNonempty
        (L := language) fiveCycleImageFamily ∧
      AvoidsGlobalFunctionalEHN fiveCycleImageFamily
        twoPointEdgeWithExtraT ∧
      twoPointEdgeTest.Irreducible ∧
      twoPointEdgeTest.IsWeakHomomorphism
        twoPointEdgeWithExtraT (id : Fin 2 → Fin 2) ∧
      ¬ twoPointEdgeTest.IsEHNHomomorphismEmbedding
        twoPointEdgeWithExtraT (id : Fin 2 → Fin 2) := by
  exact ⟨fiveCycleImageFamily_printedImageClosed,
    fiveCycleImageFamily_connectedNonempty,
    twoPointSide_avoids_fiveCycleImageFamily,
    twoPointEdgeTest_irreducible,
    twoPointTest_weak_notEHN_forbiddenFreeSide.1,
    twoPointTest_weak_notEHN_forbiddenFreeSide.2⟩

end AllThoseRamseyClasses.Lifts.EHNRelationalTupleGap
