import AllThoseRamseyClasses.Published.GeneratedClosureProfiles2019

/-!
# Actual closed boundaries from finite weak profile overlaps

For a tuple in a closed Base, record its ACTUAL ambient closure and the
same tuple as generators. Consequently, any finite common weak profile
structure embedded in two canonical expansions supplies ONE closed
structure with full embeddings into both original sides, agreeing on
all the ORIGINAL common vertices. This derives the boundary rather
than requiring an arbitrary compatible-completion oracle.

It is a theorem about the new profile expansion. It does not assert that
ordinary unexpanded weak overlaps possess compatible closed boundaries.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Record the actual ambient closure of a tuple in a closed Base.
The original tuple, viewed in this hull, really generates it. -/
def closureProfileOfTuple2019
    {rules : ClosureDescription L} {UB : Type v}
    (Base : RelStructure L UB) (hBase : IsUClosed rules Base)
    {n : ℕ} (g : Fin n → UB) : GeneratedClosureProfile2019 rules Base where
  carrier := UClosureHull rules Base (Set.range g)
  closed := hBase.induce_UClosureHull (Set.range g)
  arity := n
  generators := fun i =>
    ⟨g i, subset_UClosureHull rules Base (Set.range g) ⟨i, rfl⟩⟩
  generating := by
    let H : Set UB := UClosureHull rules Base (Set.range g)
    let gH : Fin n → H := fun i =>
      ⟨g i, subset_UClosureHull rules Base (Set.range g) ⟨i, rfl⟩⟩
    have hRange : Set.range gH = {x : H | x.1 ∈ Set.range g} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext hi⟩
    change IsUGenerating rules (Base.induce H) (Set.range gH)
    rw [hRange]
    exact UClosureHull_induce_generated rules Base (Set.range g)

/-- Any finite weak COMMON PROFILE root embedded in the fixed Base and
another canonical expansion determines an actual CLOSED K-boundary.
Its two FULL embeddings agree on every original root vertex via q.
The common weak root need not be intrinsically closed or irreducible. -/
theorem closureProfile2019_common_weak_root_closed_boundary
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L} {UB X Y : Type v}
    [Fintype X]
    (Base : RelStructure L UB) (Right : RelStructure L Y)
    (hBase : IsUClosed rules Base) (hBaseK : K Base)
    (hHer : ClosedUHereditary K rules)
    (Common : RelStructure (closureProfileLanguage2019 rules Base) X)
    (sL : Embedding Common (closureProfileExpansion2019 rules Base Base))
    (sR : Embedding Common (closureProfileExpansion2019 rules Base Right)) :
    ∃ (H : Set UB) (aL : Embedding (Base.induce H) Base)
      (aR : Embedding (Base.induce H) Right) (q : X → H),
      IsUClosed rules (Base.induce H) ∧ K (Base.induce H) ∧
      (∀ x, aL (q x) = sL x) ∧ (∀ x, aR (q x) = sR x) := by
  classical
  let enum : Fin (Fintype.card X) → X := (Fintype.equivFin X).symm
  let g : Fin (Fintype.card X) → UB := fun i => sL (enum i)
  let p : GeneratedClosureProfile2019 rules Base := closureProfileOfTuple2019 Base hBase g
  let aL : Embedding (Base.induce p.carrier) Base := inclusion Base p.carrier
  have hLeft : ∀ i : Fin p.arity, aL (p.generators i) = sL (enum i) :=
    fun _ => rfl
  obtain ⟨aR, hRight⟩ := closureProfile2019_transport_boundary_record
    Base Common Base Right sL sR p enum aL hLeft
  let q : X → p.carrier := fun x => p.generators ((Fintype.equivFin X) x)
  have hQL : ∀ x, aL (q x) = sL x := by
    intro x
    simpa [q, enum] using hLeft ((Fintype.equivFin X) x)
  have hQR : ∀ x, aR (q x) = sR x := by
    intro x
    simpa [q, enum] using hRight ((Fintype.equivFin X) x)
  exact ⟨p.carrier, aL, aR, q, p.closed,
    hHer (Base.induce p.carrier) Base hBaseK p.closed aL, hQL, hQR⟩

/-- The canonical profile expansion of a finite closed Base has every
induced subset ORDINARY irreducible. A profile on an enumeration of the
subset supplies one tuple witnessing all its pairs. No closure of the
subset is silently inserted into its vertex carrier. -/
theorem closureProfile2019_base_hereditarily_irreducible
    {rules : ClosureDescription L} {UB : Type v} [Finite UB]
    (Base : RelStructure L UB) (hBase : IsUClosed rules Base) :
    HereditarilyIrreducible (closureProfileExpansion2019 rules Base Base) := by
  classical
  intro S
  letI : Fintype S := Fintype.ofFinite S
  let enum : Fin (Fintype.card S) → S := (Fintype.equivFin S).symm
  let g : Fin (Fintype.card S) → UB := fun i => (enum i).1
  let p : GeneratedClosureProfile2019 rules Base := closureProfileOfTuple2019 Base hBase g
  intro x y _
  refine ⟨.inr p, enum, (Fintype.equivFin S) x,
    (Fintype.equivFin S) y, ?_, ?_, ?_⟩
  · exact ⟨inclusion Base p.carrier, fun _ => rfl⟩
  · exact (Fintype.equivFin S).symm_apply_apply x
  · exact (Fintype.equivFin S).symm_apply_apply y

end AllThoseRamseyClasses.Published
