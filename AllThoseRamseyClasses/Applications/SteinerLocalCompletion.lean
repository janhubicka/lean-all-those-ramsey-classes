import AllThoseRamseyClasses.Applications.SteinerStrongAmalgamation
import AllThoseRamseyClasses.Published.Coordinated2019ProfileSparseWitness
import AllThoseRamseyClasses.Applications.SteinerAmbientRamsey
import AllThoseRamseyClasses.Applications.SteinerTripleIsomorphism
import PartiteConstruction.Ramsey.ClosureIrreducibleHulls
import Mathlib.Order.Prod.Lex.Basic

/-!
# Exact locally finite completion for freely ordered partial Steiner triples

The decisive observation is that the closure of any *positive relation
tuple* is an intrinsically closed U-irreducible induced test, since the
tuple itself is an ordinary irreducible seed. Corrected 2019 (4b) puts
this entire closed hull in the Steiner class.

The ambient finite ordered control supplies a map strict on all old
positive order pairs. Ordering the weak candidate lexicographically by
the control image and an arbitrary vertex tie-breaker preserves these
positive pairs. On every old closed irreducible K-test this order is
already determined, so the test embeds fully into the new structure.

Consequently ALL Steiner block laws and marked-pair normal forms
transfer from the verified local K-tests. Block uniqueness itself
comes from intrinsic U-closedness. The completion is on the SAME
vertex set; every old full B-copy remains full, and none of the
original weak test vertices is replaced by a U-closure.

In fact the local implication is established already for n=0:
the (4c) weak-test antecedent is never used. This is a statement
about the *specific Steiner class*, not an assertion that (4c) is
redundant in the general multiamalgamation theorem.
-/

namespace AllThoseRamseyClasses.Applications.SteinerTriples

open StructuralRamsey
open StructuralRamsey.RelStructure
open AllThoseRamseyClasses.Published

/-- The literal closure hull of a single positive tuple is a closed,
intrinsically irreducible K-test; no small-test completion is assumed. -/
private theorem steiner_tuple_hull_in_class
    {V : Type} (C : RelStructure Lang V)
    (hClosed : IsUClosed blockRules C)
    (hCovered : CorrectedUIrreduciblesIn orderedSteinerClass blockRules C)
    (R : Symbol) (t : Fin (Lang.arity R) → V)
    (ht : C.rel R t) :
    ∃ S : Set V,
      (∀ i, t i ∈ S) ∧ orderedSteinerClass (C.induce S) := by
  classical
  let Seed : Set V := Set.range t
  have hSeedIrr : (C.induce Seed).Irreducible := by
    intro x y hxy
    obtain ⟨i, hi⟩ := x.2
    obtain ⟨j, hj⟩ := y.2
    refine ⟨R, (fun k => ⟨t k, ⟨k, rfl⟩⟩), i, j, ?_, ?_, ?_⟩
    · change C.rel R
        (Subtype.val ∘ (fun k => (⟨t k, ⟨k, rfl⟩⟩ : Seed)))
      convert ht using 1
      funext k
      rfl
    · apply Subtype.ext
      exact hi
    · apply Subtype.ext
      exact hj
  let S : Set V := UClosureHull blockRules C Seed
  refine ⟨S, ?_, ?_⟩
  · intro i
    exact subset_UClosureHull blockRules C Seed ⟨i, rfl⟩
  · exact hCovered S (hClosed.induce_UClosureHull Seed)
      (hClosed.irreducibleSeed_hull_isUIrreducible Seed hSeedIrr)

/-- Completion of every weak closed candidate satisfying the
coordinated (4b) hypotheses; the cutoff-zero small tests are not
used. Unlike the poset example, no long-path closure of the
non-order relations is needed. -/
theorem orderedSteiner_exactLocal_zero
    {X Y : Type} [Finite X] [Finite Y]
    (B : RelStructure Lang X) (C0 : RelStructure Lang Y)
    (hB : orderedSteinerClass B) (hC0 : orderedAmbientClass C0) :
    InducedClosedULocalCompletionAt
      orderedSteinerClass blockRules B C0 0 := by
  intro V hFiniteV C hClosed hControl hCovered _hSmall
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  letI : Fintype V := Fintype.ofFinite V
  letI : LinearOrder Y := ambientLinearOrder C0 hC0
  obtain ⟨_hC0Irred, f, hf⟩ := hControl
  let key : V → Y ×ₗ Fin (Fintype.card V) :=
    fun x => toLex (f x, Fintype.equivFin V x)
  have hKeyInjective : Function.Injective key := by
    intro x y hxy
    apply (Fintype.equivFin V).injective
    exact congrArg (fun z => (ofLex z).2) hxy
  let o : LinearOrder V := LinearOrder.lift' key hKeyInjective
  letI : LinearOrder V := o
  have hOldOrder : ∀ x y : V, edge C .order x y →
      @LT.lt V o.toLT x y := by
    intro x y hxy
    have hOrderInControl : edge C0 .order (f x) (f y) := by
      change C0.rel .order ![f x, f y]
      have ht : f ∘ ![x,y] = ![f x,f y] := by
        funext i
        fin_cases i <;> rfl
      rw [← ht]
      exact hf.1 .order ![x,y] hxy
    have hControlLt : f x < f y :=
      (ambientLinearOrder_lt_iff C0 hC0 (f x) (f y)).mpr hOrderInControl
    change key x < key y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hControlLt)
  let Target : RelStructure Lang V := {
    rel := fun
      | .order, t => @LT.lt V o.toLT (t 0) (t 1)
      | .covered, t => C.rel .covered t
      | .block, t => C.rel .block t
  }
  have hInducedOrder (S : Set V) (x y : S)
      (h : edge (C.induce S) .order x y) :
      edge C .order x.1 y.1 := by
    change C.rel .order ![x.1, y.1]
    change C.rel .order (Subtype.val ∘ ![x,y]) at h
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hEmbOnKTest (S : Set V)
      (hKS : orderedSteinerClass (C.induce S)) :
      Embedding (C.induce S) Target := by
    refine {
      toFun := Subtype.val
      injective := Subtype.val_injective
      map_rel_iff := ?_
    }
    intro R t
    cases R with
    | order =>
        have ht : t = ![t 0,t 1] := by
          funext i
          fin_cases i <;> rfl
        rw [ht]
        change (@LT.lt V o.toLT (t 0).1 (t 1).1) ↔
          edge (C.induce S) .order (t 0) (t 1)
        constructor
        · intro hnew
          have hne : t 0 ≠ t 1 := by
            intro heq
            have hVal : (t 0).1 = (t 1).1 := congrArg Subtype.val heq
            exact (ne_of_lt hnew) hVal
          rcases hKS.order_total (t 0) (t 1) hne with h | h
          · exact h
          · exact (lt_asymm hnew
              (hOldOrder (t 1).1 (t 0).1 (hInducedOrder S (t 1) (t 0) h))).elim
        · intro hold
          exact hOldOrder (t 0).1 (t 1).1 (hInducedOrder S (t 0) (t 1) hold)
    | covered =>
        exact Iff.rfl
    | block =>
        exact Iff.rfl
  -- The non-order predicates stay literally unchanged on induced sets.
  have hCoveredFromInduce (S : Set V) (x y : S)
      (h : edge (C.induce S) .covered x y) :
      edge Target .covered x.1 y.1 := by
    change C.rel .covered ![x.1, y.1]
    change C.rel .covered (Subtype.val ∘ ![x,y]) at h
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hTripleFromInduce (S : Set V) (x y z : S)
      (h : triple (C.induce S) x y z) :
      triple Target x.1 y.1 z.1 := by
    change C.rel .block ![x.1, y.1, z.1]
    change C.rel .block (Subtype.val ∘ ![x,y,z]) at h
    convert h using 1
    funext i
    fin_cases i <;> rfl
  have hOrderFromInduce (S : Set V) (x y : S)
      (h : edge (C.induce S) .order x y) :
      edge Target .order x.1 y.1 := by
    have hOld : edge C .order x.1 y.1 :=
      hInducedOrder S x y h
    exact hOldOrder x.1 y.1 hOld
  have hTarget : orderedSteinerClass Target := by
    refine {
      finite := inferInstance
      order_irrefl := ?_
      order_trans := ?_
      order_total := ?_
      covered_implies_order := ?_
      covered_root := ?_
      block_valid := ?_
      block_distinct := ?_
      covered_has_block := ?_
      block_unique := ?_
      other_pairs := ?_
    }
    · intro x hxx
      exact (lt_irrefl x hxx).elim
    · intro x y z hxy hyz
      exact lt_trans hxy hyz
    · intro x y hne
      exact lt_or_gt_of_ne hne
    · intro x y hxy
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .covered ![x,y] hxy
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      have hInside : edge (C.induce S) .covered xS yS := by
        change C.rel .covered (Subtype.val ∘ ![xS, yS])
        have h0 : C.rel .covered ![x, y] := hxy
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      exact hOrderFromInduce S xS yS (hKS.covered_implies_order xS yS hInside)
    · intro x y hxy
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .covered ![x,y] hxy
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      have hInside : edge (C.induce S) .covered xS yS := by
        change C.rel .covered (Subtype.val ∘ ![xS, yS])
        have h0 : C.rel .covered ![x, y] := hxy
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨e,he0,he1⟩ := hKS.covered_root xS yS hInside
      refine ⟨(hEmbOnKTest S hKS).comp e, ?_, ?_⟩
      · change (e 0).1 = x
        exact congrArg Subtype.val he0
      · change (e 1).1 = y
        exact congrArg Subtype.val he1
    · intro x y z hxyz
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .block ![x,y,z] hxyz
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      let zS : S := ⟨z,hS 2⟩
      have hInside : triple (C.induce S) xS yS zS := by
        change C.rel .block (Subtype.val ∘ ![xS, yS, zS])
        have h0 : C.rel .block ![x, y, z] := hxyz
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      exact hCoveredFromInduce S xS yS (hKS.block_valid xS yS zS hInside)
    · intro x y z hxyz
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .block ![x,y,z] hxyz
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      let zS : S := ⟨z,hS 2⟩
      have hInside : triple (C.induce S) xS yS zS := by
        change C.rel .block (Subtype.val ∘ ![xS, yS, zS])
        have h0 : C.rel .block ![x, y, z] := hxyz
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨hxy,hxz,hyz⟩ := hKS.block_distinct xS yS zS hInside
      exact ⟨fun h => hxy (Subtype.ext h),
        fun h => hxz (Subtype.ext h),
        fun h => hyz (Subtype.ext h)⟩
    · intro x y hxy
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .covered ![x,y] hxy
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      have hInside : edge (C.induce S) .covered xS yS := by
        change C.rel .covered (Subtype.val ∘ ![xS, yS])
        have h0 : C.rel .covered ![x, y] := hxy
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨zS,hz⟩ := hKS.covered_has_block xS yS hInside
      exact ⟨zS.1, hTripleFromInduce S xS yS zS hz⟩
    · intro x y z w hz hw
      exact steiner_block_unique_of_UClosed C hClosed hz hw
    · intro x y z hxyz
      obtain ⟨S, hS, hKS⟩ :=
        steiner_tuple_hull_in_class C hClosed hCovered .block ![x,y,z] hxyz
      let xS : S := ⟨x,hS 0⟩
      let yS : S := ⟨y,hS 1⟩
      let zS : S := ⟨z,hS 2⟩
      have hInside : triple (C.induce S) xS yS zS := by
        change C.rel .block (Subtype.val ∘ ![xS, yS, zS])
        have h0 : C.rel .block ![x, y, z] := hxyz
        convert h0 using 1
        funext i
        fin_cases i <;> rfl
      obtain ⟨hXZ,hYZ⟩ := hKS.other_pairs xS yS zS hInside
      constructor
      · rcases hXZ with ⟨htr,hord⟩ | ⟨htr,hord⟩
        · exact Or.inl ⟨hTripleFromInduce S xS zS yS htr,
            hOrderFromInduce S xS zS hord⟩
        · exact Or.inr ⟨hTripleFromInduce S zS xS yS htr,
            hOrderFromInduce S zS xS hord⟩
      · rcases hYZ with ⟨htr,hord⟩ | ⟨htr,hord⟩
        · exact Or.inl ⟨hTripleFromInduce S yS zS xS htr,
            hOrderFromInduce S yS zS hord⟩
        · exact Or.inr ⟨hTripleFromInduce S zS yS xS htr,
            hOrderFromInduce S zS yS hord⟩
  refine ⟨V, inferInstance, Target, hTarget, (fun x : V => x), ?_⟩
  intro b
  let bTarget : Embedding B Target := {
    toFun := b
    injective := b.injective
    map_rel_iff := by
      intro R t
      cases R with
      | order =>
          have ht : t = ![t 0,t 1] := by
            funext i
            fin_cases i <;> rfl
          rw [ht]
          change (@LT.lt V o.toLT (b (t 0)) (b (t 1))) ↔
            edge B .order (t 0) (t 1)
          constructor
          · intro hnew
            have hne : t 0 ≠ t 1 := by
              intro heq
              have heq' : b (t 0) = b (t 1) := congrArg b heq
              exact (ne_of_lt hnew) heq'
            rcases hB.order_total (t 0) (t 1) hne with h | h
            · exact h
            · exact (lt_asymm hnew
                (hOldOrder (b (t 1)) (b (t 0))
                  ((edge_embedding_iff b .order (t 1) (t 0)).mpr h))).elim
          · intro h
            exact hOldOrder (b (t 0)) (b (t 1))
              ((edge_embedding_iff b .order (t 0) (t 1)).mpr h)
      | covered =>
          exact b.map_rel_iff .covered t
      | block =>
          exact b.map_rel_iff .block t
  }
  exact ⟨bTarget, fun _ => rfl⟩

/-- All hypotheses of corrected 2019 Theorem 2.18 are discharged for
the actual finite class of freely ordered partial Steiner triples.
The strict linear vertex order is freely chosen, not admissible. -/
theorem orderedSteiner_isCoordinated2019Multiamalgamation :
    IsCoordinated2019MultiamalgamationClass
      orderedAmbientClass orderedSteinerClass blockRules := by
  refine ⟨{
    subset := ?_
    finite := ?_
    closed := ?_
    hereditary := ?_
    strong := orderedSteinerClass_strongAmalgamation
    localCompletion := ?_
  }, orderedSteiner_isomorphismClosed⟩
  · intro X A hA
    exact orderedSteiner_subset_ambient A hA
  · intro X A hA
    exact hA.finite
  · intro X A hA
    exact orderedSteiner_isUClosed A hA
  · intro X A hA S hClosed
    exact orderedSteiner_of_closed_embedding
      (A.induce S) A hA hClosed (inclusion A S)
  · intro X Y hFiniteX hFiniteY B C0 hB hC0
    exact ⟨0, orderedSteiner_exactLocal_zero B C0 hB hC0⟩

/-- The class of finite freely ordered partial Steiner triple systems
with full marked-pair strong embeddings is Ramsey. -/
theorem orderedSteiner_isRamsey :
    FiniteRamseyClass orderedSteinerClass := by
  apply coordinated2019_ramsey_by_profile_sparsening
    orderedAmbientClass orderedSteinerClass blockRules
    orderedSteinerAmbient_isRamsey
  · intro X C hC
    exact steinerAmbient_irreducible C hC
  · exact orderedSteiner_isCoordinated2019Multiamalgamation

end AllThoseRamseyClasses.Applications.SteinerTriples
