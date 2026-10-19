import AllThoseRamseyClasses.Lifts.GlobalIrreducibleForbiddenStrongAmalgamation
import PartiteConstruction.Ramsey.FreeAmalgamationFunctionsAllArity

/-!
# Ramsey theorem for irreducible forbidden EHN sources

For the irreducible-source special case of the 2019 Section 3
forbidden-family construction, no auxiliary homogenizing relations
are actually necessary. The existing unconditional shadow lemma
proves that Forb_EHN(F) is a native full functional free-amalgamation
class: if an irreducible forbidden source mapped weakly to a free
amalgam, the EHN condition would produce a full embedding of the
ENTIRE source, forcing it into one side.

The verified all-arity Evans--Hubicka--Nesetril functional Ramsey
theorem can therefore be applied directly after freely adjoining
an external linear order. This is a genuine finite Ramsey-arrow
theorem for arbitrary (possibly infinite) forbidden families of
finite native irreducible structures. It needs NO regularity,
image-closure, or global quotient-piece setoid assumption.

This theorem does NOT address reducible forbidden sources, where
the canonical global lift and its unresolved shadow avoidance
lemma remain necessary. Original function value fibres and the
distinction between weak EHN maps and full embeddings are preserved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u w
variable {L : Language.{u}}

/-- Forb_EHN(F) itself is hereditary and closed under ACTUAL native
FULL functional free amalgamation whenever F contains only finite
irreducible sources. This is stronger than the conditional global
lift shadow compatibility statement. -/
theorem globalForbiddenIrreducible_freeClass
    (F : ∀ {V : Type}, Structure L V → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F) :
    Structure.FreeAmalgamationClass
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) := by
  constructor
  · intro U V A B hB e
    exact avoidsGlobalFunctionalEHN_of_embedding F e hB
  · intro H E G W D A B C sA sB iA iB hA hB hFree
    exact avoidsGlobalFunctionalEHN_freeAmalgam_irreducible
      F hIrred hFree hA hB

/-- Actual finite Ramsey witness for freely ordered native structures
avoiding ANY family of finite irreducible EHN forbidden sources.
All arities, partial/set-valued functions and zero-ary symbols are
handled by the already verified functional EHN Ramsey construction.

This is a proved Ramsey theorem, not a conditional theorem with a
newly postulated Ramsey-class premise. -/
theorem globalForbiddenIrreducible_freelyOrderedRamsey
    (F : ∀ {V : Type}, Structure L V → Prop)
    (hIrred : GlobalForbiddenSourcesIrreducible F)
    {UA UB : Type}
    (A : Structure L UA) (B : Structure L UB)
    [LinearOrder UA] [LinearOrder UB]
    [Finite UA] [Finite UB]
    (hA : AvoidsGlobalFunctionalEHN F A)
    (hB : AvoidsGlobalFunctionalEHN F B)
    (κ : Type w) [Fintype κ] [Nonempty κ] :
    ∃ (W : Type) (_ : Finite W) (o : LinearOrder W)
      (C : Structure L W),
      AvoidsGlobalFunctionalEHN F C ∧
        Structure.Arrow A.withLinearOrder B.withLinearOrder
          (@Structure.withLinearOrder _ W C o.toLT) κ := by
  exact StructuralRamsey.Rooted.Structure.FreeAmalgamationClass.orderedRamsey_allArity
    (globalForbiddenIrreducible_freeClass F hIrred) A B hA hB κ

end AllThoseRamseyClasses.Lifts
