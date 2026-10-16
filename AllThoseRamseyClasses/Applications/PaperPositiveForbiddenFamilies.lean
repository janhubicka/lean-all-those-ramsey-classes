import AllThoseRamseyClasses.Applications.PaperForbiddenFamilies

/-!
# Positive forbidden families via all full extensions

A positive copy is an injective relation-preserving map, not
necessarily relation-reflecting. Full/induced copies are more
restrictive. For an irreducible forbidden pattern F, forbidding
positive copies is EQUIVALENT to forbidding full embeddings of
*all relational extensions* of F on its own carrier.

The family of such extensions is allowed to be infinite. Each
forbidden member may have its own finite carrier type and arity
profile, and the target is not assumed to be oriented, loopless
or devoid of opposite edges.

This lets the verified full-forbidden-family free-amalgamation
theorem prove ordered Ramsey for the usual positive-subgraph
avoidance notion without rebuilding any partite construction.
-/

namespace AllThoseRamseyClasses.Applications.ForbiddenPatterns

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v w
variable {L : RelLanguage.{u}} {I : Type w} {P : I → Type v}

/-- An injective positive homomorphism of relational structures.
Negative tuples are NOT reflected. -/
def HasPositiveCopy {U V : Type v}
    (A : RelStructure L U) (B : RelStructure L V) : Prop :=
  ∃ f : U → V, Function.Injective f ∧
    ∀ R t, A.rel R t → B.rel R (f ∘ t)

/-- Every full embedding is a positive copy. -/
theorem hasPositiveCopy_of_embedding {U V : Type v}
    {A : RelStructure L U} {B : RelStructure L V}
    (e : Embedding A B) : HasPositiveCopy A B :=
  ⟨e, e.injective, fun R t h => (e.map_rel_iff R t).mpr h⟩

/-- Positive-free class: no forbidden F has an injective positive
copy. This is distinct from the full-embedding avoidance predicate. -/
def ForbPositiveFamily
    (K : StructureClass.{u,v} (L := L))
    (Forbidden : (i : I) → RelStructure L (P i)) :
    StructureClass.{u,v} (L := L) :=
  fun C => K C ∧ ∀ i : I, ¬ HasPositiveCopy (Forbidden i) C

/-- All possible FULL relational structures extending a forbidden
positive pattern. The index carries the original forbidden member,
its extension, and the positive-relation inclusion certificate. -/
abbrev PositiveExtensionIndices
    (Forbidden : (i : I) → RelStructure L (P i)) :=
  Sigma fun i : I =>
    {H : RelStructure L (P i) //
      ∀ R t, (Forbidden i).rel R t → H.rel R t}

/-- The forbidden full pattern belonging to an extension index. -/
def positiveExtensionPattern
    (Forbidden : (i : I) → RelStructure L (P i))
    (q : PositiveExtensionIndices Forbidden) :
    RelStructure L (P q.1) :=
  q.2.1

/-- Exact equivalence of forbidding positive copies and forbidding
every FULL extension. No finite-language or finite-index assumption. -/
theorem forbPositiveFamily_iff_forbFullExtensions
    (K : StructureClass.{u,v} (L := L))
    (Forbidden : (i : I) → RelStructure L (P i))
    {V : Type v} (C : RelStructure L V) :
    ForbPositiveFamily K Forbidden C ↔
      ForbFamily K (positiveExtensionPattern Forbidden) C := by
  constructor
  · rintro ⟨hK, hno⟩
    refine ⟨hK, ?_⟩
    intro q ⟨e⟩
    exact hno q.1
      ⟨e, e.injective,
        fun R t h => (e.map_rel_iff R t).mpr (q.2.2 R t h)⟩
  · rintro ⟨hK, hno⟩
    refine ⟨hK, ?_⟩
    intro i ⟨f, hf, hPos⟩
    let H : RelStructure L (P i) := {
      rel := fun R t => C.rel R (f ∘ t)
    }
    have hExt : ∀ R t, (Forbidden i).rel R t → H.rel R t := hPos
    let q : PositiveExtensionIndices Forbidden := ⟨i, ⟨H, hExt⟩⟩
    let e : Embedding H C := {
      toFun := f
      injective := hf
      map_rel_iff := fun _ _ => Iff.rfl
    }
    exact hno q ⟨e⟩

/-- Every full extension of an irreducible forbidden pattern
remains irreducible: each Gaifman witness survives by positive
relation inclusion. -/
theorem positiveExtension_irreducible
    (Forbidden : (i : I) → RelStructure L (P i))
    (hF : ∀ i : I, (Forbidden i).Irreducible)
    (q : PositiveExtensionIndices Forbidden) :
    (positiveExtensionPattern Forbidden q).Irreducible := by
  intro x y hxy
  obtain ⟨R, t, a, b, ht, hx, hy⟩ := hF q.1 x y hxy
  exact ⟨R, t, a, b, q.2.2 R t ht, hx, hy⟩

/-- A POSITIVE-free hereditary free-amalgamation class, derived
rather than postulated. This is the class property needed for the
ordered Ramsey theorem, including potentially infinite forbidden
families of variable sizes. -/
theorem freeAmalgamation_of_positive_irreducible_family
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : (i : I) → RelStructure L (P i)}
    (hK : FreeAmalgamationClass K)
    (hF : ∀ i : I, (Forbidden i).Irreducible) :
    FreeAmalgamationClass (ForbPositiveFamily K Forbidden) := by
  have hFull :
      FreeAmalgamationClass
        (ForbFamily K (positiveExtensionPattern Forbidden)) :=
    freeAmalgamation_of_irreducible_family hK
      (positiveExtension_irreducible Forbidden hF)
  refine ⟨?_, ?_⟩
  · intro U V A B hB e
    exact (forbPositiveFamily_iff_forbFullExtensions
      K Forbidden A).mpr
      (hFull.hereditary
        ((forbPositiveFamily_iff_forbFullExtensions
          K Forbidden B).mp hB) e)
  · intro H E F W D A B C sA sB iA iB hA hB hFree
    exact (forbPositiveFamily_iff_forbFullExtensions
      K Forbidden C).mpr
        (hFull.free
          ((forbPositiveFamily_iff_forbFullExtensions
            K Forbidden A).mp hA)
          ((forbPositiveFamily_iff_forbFullExtensions
            K Forbidden B).mp hB)
          hFree)

/-- The fully proved Ramsey theorem for POSITIVE avoidance
of an arbitrary family of irreducible relational patterns.
Unlike induced avoidance, no negative tuple reflection is
required of the forbidden injective maps. The Ramsey copies
themselves are still ordinary FULL embeddings. -/
theorem orderedRamsey_avoiding_positive_irreducible_family
    {K : StructureClass.{u,v} (L := L)}
    {Forbidden : (i : I) → RelStructure L (P i)}
    (hK : FreeAmalgamationClass K)
    (hF : ∀ i : I, (Forbidden i).Irreducible)
    {U V : Type v} [Finite U] [Finite V]
    [LinearOrder U] [LinearOrder V]
    (A : RelStructure L U) (B : RelStructure L V)
    (hA : ForbPositiveFamily K Forbidden A)
    (hB : ForbPositiveFamily K Forbidden B)
    (κ : Type*) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type v) (_ : Finite W) (o : LinearOrder W)
      (C : RelStructure L W),
      ForbPositiveFamily K Forbidden C ∧
      StructuralRamsey.Arrow A.ordered B.ordered
        (@RelStructure.ordered L W C o.toLT) κ :=
  FreeAmalgamationClass.orderedRamsey
    (freeAmalgamation_of_positive_irreducible_family hK hF)
    A B hA hB κ

end AllThoseRamseyClasses.Applications.ForbiddenPatterns
