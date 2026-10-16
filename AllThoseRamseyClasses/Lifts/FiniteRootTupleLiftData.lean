import AllThoseRamseyClasses.Lifts.FunctionalLiftLanguageBig

/-!
# Finite labelled relation lifts supported only on distinct root tuples

The precompactness step of Section 3 ("Construction of Ramsey lifts")
has a simple independent core: on a fixed finite vertex carrier,
only finitely many new relations with FINITELY MANY symbols in each
arity can be nonempty, PROVIDED every added relation tuple has
pairwise distinct coordinates.

Merely requiring finitely many new symbols of each arity is NOT
enough if repeated coordinates are permitted at arbitrarily large
arities: even a one-element carrier then supports infinitely many
independent relation predicates.

Here the finite-support theorem is stated once with a finite active
index type. The arity-counting corollary constructs such an active
index type from finite arity fibres and the pigeonhole inequality
for injective root tuples. No finite total signature is assumed.

All original partial/set-valued functions are fixed by the functional
shadow, so the only varying information is the new relation data.
The further passage from labelled fibres to isomorphism-type
precompactness uses this finite labelled upper bound.
-/

namespace AllThoseRamseyClasses.Lifts

universe u v w

/-- All choices of new relation interpretations on a fixed carrier. -/
abbrev ExtraRelationData (New : Type u) (ar : New → ℕ)
    (V : Type v) :=
  ∀ i : New, (Fin (ar i) → V) → Prop

/-- The precise injective-root condition in the canonical lift. -/
def ExtraRelationsDistinctRoots
    {New : Type u} {ar : New → ℕ} {V : Type v}
    (extra : ExtraRelationData New ar V) : Prop :=
  ∀ (i : New) (xs : Fin (ar i) → V),
    extra i xs → Function.Injective xs

/-- All possible labelled interpretations satisfying distinct roots.
No forbidden-pattern consistency restriction is imposed: any
actual maximal canonical lift embeds into this larger candidate set. -/
abbrev DistinctRootExtraData (New : Type u)
    (ar : New → ℕ) (V : Type v) :=
  {extra : ExtraRelationData New ar V //
    ExtraRelationsDistinctRoots extra}

/-- If every potentially nonempty new relation symbol is covered
by a finite index type, the number of entire labelled relation
interpretations is finite. The proof uses the observation function
on the finite active indices and shows it is injective. -/
theorem finite_distinctRootExtraData_of_active
    {New : Type u} {ar : New → ℕ} {V : Type v}
    [Finite V] {Active : Type w} [Finite Active]
    (index : Active → New)
    (hcover : ∀ (i : New) (xs : Fin (ar i) → V),
      Function.Injective xs → ∃ a : Active, index a = i) :
    Finite (DistinctRootExtraData New ar V) := by
  classical
  let Snapshot :=
    ∀ a : Active, (Fin (ar (index a)) → V) → Prop
  haveI : Finite Snapshot := inferInstance
  let observe : DistinctRootExtraData New ar V → Snapshot :=
    fun X a xs => X.1 (index a) xs
  apply Finite.of_injective observe
  intro X Y h
  apply Subtype.ext
  funext i xs
  by_cases hidx : ∃ a : Active, index a = i
  · obtain ⟨a, ha⟩ := hidx
    subst i
    exact congrArg (fun snap : Snapshot => snap a xs) h
  · apply propext
    constructor
    · intro hX
      exact False.elim
        (hidx (hcover i xs (X.2 i xs hX)))
    · intro hY
      exact False.elim
        (hidx (hcover i xs (Y.2 i xs hY)))

/-- Finitely many symbols at EVERY fixed arity suffice, even when
the total expanded language has infinitely many symbols. The
injective-root requirement forces all active arities to be at
most the cardinality of the finite carrier. -/
theorem finite_distinctRootExtraData_of_finite_arity_fibres
    (New : Type u) (ar : New → ℕ) (V : Type v)
    [Fintype V]
    (hFibres : ∀ n : ℕ, Finite {i : New // ar i = n}) :
    Finite (DistinctRootExtraData New ar V) := by
  classical
  let m : ℕ := Fintype.card V
  let Active :=
    Σ k : Fin (m + 1), {i : New // ar i = k.1}
  letI (k : Fin (m + 1)) : Finite {i : New // ar i = k.1} :=
    hFibres k.1
  haveI : Finite Active := inferInstance
  let index : Active → New := fun x => x.2.1
  apply finite_distinctRootExtraData_of_active index
  intro i xs hxs
  have hle : ar i ≤ m := by
    simpa only [Fintype.card_fin, m] using
      (Fintype.card_le_of_injective xs hxs)
  refine ⟨⟨⟨ar i, Nat.lt_succ_of_le hle⟩, ⟨i, rfl⟩⟩, rfl⟩

/-- Canonical extra relations use only injective tuples, so they
belong to the finite-support candidate class on each fixed finite
carrier whenever the arity fibres are finite. -/
def canonicalExtraData
    {L : StructuralRamsey.Language.{u}}
    (New : Type w) (ar : New → ℕ)
    (pieces : ∀ i : New,
      Set (FunctionalRootedPattern.{u,v} L (ar i)))
    {V : Type v} (A : StructuralRamsey.Structure L V) :
    DistinctRootExtraData New ar V where
  val := functionalCanonicalExtraBig L New ar pieces A
  property := by
    intro i xs h
    exact h.1

end AllThoseRamseyClasses.Lifts
