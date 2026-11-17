import AllThoseRamseyClasses.Lifts.GlobalForbiddenEHNAvoidance

/-!
# Semantic piece transfer: allowed contexts versus arbitrary contexts

A proposed repair of the 2019 piece equivalence compares incompatibility
using genuine EHN-forbidden maps in native FUNCTIONAL free amalgams.

One may try to compare only allowed rooted contexts. A key proof obligation
is what happens after an earlier piece replacement makes the complementary
context forbidden. Such a context is automatically forbidden in every
further FULL extension; no new comparison premise is needed.

This file proves that two native full extensions of the same context have
the same forbidden status if their statuses agree WHEN the context is
allowed. It retains partial functions and uses the precise original
2019 global EHN avoidance semantics. No root injectivity, quotient,
source minimizer, free-amalgam preservation or finite language is assumed.

This is ONLY the intermediate-context logic. It does NOT construct
the pieces, prove the revised equivalence regular, or verify Lemma 3.25.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u

variable {L : Language.{u}}

/-- A forbidden native functional source persists under a FULL
old-language embedding, without assuming any target-side
freeness or any properties of an arbitrary homomorphic image. -/
theorem notAvoidsGlobalFunctionalEHN_of_embedding
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VA VB : Type}
    {A : Structure L VA} {B : Structure L VB}
    (e : Structure.Embedding A B)
    (hBadA : ¬ AvoidsGlobalFunctionalEHN F A) :
    ¬ AvoidsGlobalFunctionalEHN F B := by
  intro hGoodB
  exact hBadA (avoidsGlobalFunctionalEHN_of_embedding F e hGoodB)

/-- If the old and replacement free diagrams both FULLY contain
the same rooted context, agreement of forbidden status for
ALLOWED contexts automatically extends to every context.
In the forbidden-context branch, the context's own forbidden
witness persists in the replacement. -/
theorem semanticPiece_allowedContext_iff_implies_allContexts
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VC VO VN : Type}
    (Context : Structure L VC)
    (Old : Structure L VO) (New : Structure L VN)
    (iOld : Structure.Embedding Context Old)
    (iNew : Structure.Embedding Context New)
    (hAllowedIff :
      AvoidsGlobalFunctionalEHN F Context →
        (¬ AvoidsGlobalFunctionalEHN F Old ↔
         ¬ AvoidsGlobalFunctionalEHN F New)) :
    (¬ AvoidsGlobalFunctionalEHN F Old ↔
     ¬ AvoidsGlobalFunctionalEHN F New) := by
  by_cases hAllowed : AvoidsGlobalFunctionalEHN F Context
  · exact hAllowedIff hAllowed
  · constructor
    · intro _
      exact notAvoidsGlobalFunctionalEHN_of_embedding F iNew hAllowed
    · intro _
      exact notAvoidsGlobalFunctionalEHN_of_embedding F iOld hAllowed

end AllThoseRamseyClasses.Lifts
