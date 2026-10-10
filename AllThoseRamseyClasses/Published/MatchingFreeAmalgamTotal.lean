import AllThoseRamseyClasses.Published.MatchingFreeAmalgam
import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion

/-!
# Every vertex of the free amalgam retains exactly one mate

This is a theorem about the CONCRETE relational free-amalgam carrier.
The input objects carry the total fixed-point-free matching M and E.
The full amalgam does not yet satisfy a linear order or a transitive
E relation; these two completions are separate strong-amalgamation
obligations. The matching's totality is not an assumed oracle.

The proof uses the original 2019 relational U-closure rule and its
proved existence/uniqueness, not a surrogate functional encoding.
-/

namespace AllThoseRamseyClasses.Published.PairedEquivalenceObstruction

open StructuralRamsey
open StructuralRamsey.RelStructure

/-- Every vertex in a paired structure admits the prescribed unary
closure root embedding, because E is reflexive and M and < are
irreflexive. -/
private def rootEmbedding
    {V : Type} (C : RelStructure Lang V)
    (hC : pairedClass C) (v : V) :
    Embedding mateRoot C where
  toFun := fun _ => v
  injective := by
    intro a b _
    exact Subsingleton.elim a b
  map_rel_iff := by
    intro R t
    have ht :
        ((fun _ : Fin 1 => v) ∘ t) = ![v, v] := by
      funext i
      fin_cases i <;> rfl
    cases R with
    | lt =>
      change C.rel .lt ((fun _ : Fin 1 => v) ∘ t) ↔ False
      rw [ht]
      constructor
      · exact hC.lt_irrefl v
      · exact False.elim
    | equiv =>
      change C.rel .equiv ((fun _ : Fin 1 => v) ∘ t) ↔ True
      rw [ht]
      constructor
      · intro _; trivial
      · intro _; exact hC.equiv.refl v
    | mate =>
      change C.rel .mate ((fun _ : Fin 1 => v) ∘ t) ↔ False
      rw [ht]
      constructor
      · exact hC.mate_irrefl v
      · exact False.elim

/-- Given a witness e of a root at v in ANY U-closed structure,
there exists exactly one output of the actual matching relation
M rooted at v. No ambient E/order axioms are needed for the target. -/
private theorem mate_existsUnique_of_root
    {W : Type} (C : RelStructure Lang W)
    (hC : IsUClosed mateRules C)
    (v : W) (e : Embedding mateRoot C)
    (he : e 0 = v) :
    ∃! w : W, edge C .mate v w := by
  obtain ⟨t, ht, hUnique⟩ :=
    (hC mateRule (by simp [mateRules])).2 e
  let w : W := t 1
  have hv : t 0 = v := by
    calc
      t 0 = e 0 := ht.2 0
      _ = v := he
  refine ⟨w, ?_, ?_⟩
  · change C.rel .mate ![v, w]
    have htuple : t = ![v, w] := by
      funext i
      fin_cases i
      · exact hv
      · rfl
    rw [← htuple]
    exact ht.1
  · intro z hz
    have hzRel : C.rel mateRule.symbol ![v, z] := hz
    have hzRoot : ∀ k : Fin mateRule.rootSize,
        (![v, z] : Fin (Lang.arity mateRule.symbol) → W)
          (k.castLE mateRule.rootLE) = e k := by
      intro k
      fin_cases k
      exact he.symm
    have hEq : ![v, z] = t := hUnique ![v, z] ⟨hzRel, hzRoot⟩
    exact congrFun hEq 1

/-- The canonical relational free amalgam preserves TOTAL matching.
This does not yet establish its E-equivalence or complete order. -/
theorem freeAmalgam_mate_total
    {H E F : Type}
    (D : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (hD : pairedClass D)
    (hLeft : pairedClass Left)
    (hRight : pairedClass Right)
    (sL : Embedding D Left) (sR : Embedding D Right) :
    ∀ v : FreeAmalgam.Vertex D Left Right sL sR,
      ∃! w, edge (FreeAmalgam.amalgam D Left Right sL sR) .mate v w := by
  classical
  let C := FreeAmalgam.amalgam D Left Right sL sR
  let l := FreeAmalgam.leftEmbedding D Left Right sL sR
  let r := FreeAmalgam.rightEmbedding D Left Right sL sR
  have hClosed : IsUClosed mateRules C :=
    freeAmalgam_matching_isUClosed D Left Right
      hD hLeft hRight sL sR
  intro v
  have hroot : ∃ e : Embedding mateRoot C, e 0 = v := by
    rcases (FreeAmalgam.isFreeAmalgam D Left Right sL sR).covers v with
        ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨l.comp (rootEmbedding Left hLeft a), ?_⟩
      exact ha.symm
    · refine ⟨r.comp (rootEmbedding Right hRight b), ?_⟩
      exact hb.symm
  obtain ⟨e, he⟩ := hroot
  exact mate_existsUnique_of_root C hClosed v e he

end AllThoseRamseyClasses.Published.PairedEquivalenceObstruction
