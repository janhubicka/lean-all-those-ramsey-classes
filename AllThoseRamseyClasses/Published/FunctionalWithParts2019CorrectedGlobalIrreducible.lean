import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedSourceCertificate
import AllThoseRamseyClasses.Published.FunctionalWithParts2019CanonicalKIso
import AllThoseRamseyClasses.Published.InducedClosed2019TestNormalization

/-!
# Track C: when corrected (4b) actually forces GLOBAL H-membership

The source certificate normalizes the OLD presentation of an arbitrary
U-closed, corrected-(4b)-covered relational candidate. It does not
assert the entire candidate belongs to the genuine class H: (4b)
only checks closed U-irreducible induced substructures.

If the candidate C itself is U-irreducible and H is closed under
genuine part-preserving isomorphisms, (4b) DOES force global
canonical K(H) membership. We must explicitly transport membership
from C induced on its FULL carrier to C via the isomorphism, because
bare Lean StructureClass predicates have no automatic invariance.

This theorem identifies the exact extra global irreducibility
assumption. It is not imposed on all local-axiom candidates, which
may be U-reducible and are precisely the difficult case.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Corrected (4b) plus U-closedness, global U-irreducibility,
and ACTUAL original H-isomorphism invariance forces the entire
candidate to be a canonical genuinely partial H-member.
No arbitrary closure hull or proper weak restriction is used. -/
theorem genuineTagged2019_globalK_of_correctedCovered_UIrreducible
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hUIrr :
      IsUIrreducible
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hIso : GenuinePartiteIsomorphismClosed2019 H) :
    canonicalGenuineTagged2019Class H C := by
  classical
  let rules := (L.withParts Parts).wholeMaskClosureRules Parts
  let S : Set V := Set.univ
  let e : RelStructure.Embedding C (C.induce S) := {
    toFun := fun x => ⟨x, Set.mem_univ x⟩
    injective := by
      intro x y he
      exact congrArg Subtype.val he
    map_rel_iff := fun _ _ => Iff.rfl
  }
  have hSurj : Function.Surjective e := by
    intro x
    refine ⟨x.1, ?_⟩
    apply Subtype.ext
    rfl
  have hSClosed : IsUClosed rules (C.induce S) :=
    isUClosed_of_surjective_embedding e hSurj hClosed
  have hSIrred : IsUIrreducible rules (C.induce S) :=
    uIrreducible_of_surjective_embedding_2019 e hSurj hClosed hUIrr
  have hSK : canonicalGenuineTagged2019Class H (C.induce S) :=
    hCovered S hSClosed hSIrred
  exact (canonicalGenuineTagged2019Class_isomorphismClosed
    H hIso) C (C.induce S) e hSurj hSK

/-- Ordinary (Gaifman) irreducibility is enough, because it implies
U-irreducibility for every closure description. Consequently (4b)
already implies genuine global H-membership of an ordinary
irreducible closed candidate. -/
theorem genuineTagged2019_globalK_of_correctedCovered_irreducible
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hIrred : C.Irreducible)
    (hIso : GenuinePartiteIsomorphismClosed2019 H) :
    canonicalGenuineTagged2019Class H C :=
  genuineTagged2019_globalK_of_correctedCovered_UIrreducible
    H C hClosed hCovered
    (hIrred.isUIrreducible
      ((L.withParts Parts).wholeMaskClosureRules Parts))
    hIso

end AllThoseRamseyClasses.Published
