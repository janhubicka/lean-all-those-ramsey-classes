import AllThoseRamseyClasses.Lifts.FunctionalCopywiseRamseyTransfer
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceStrongAmalgamation

/-!
# Track E: exact Ramsey-transfer obligation for maximal finite-family traces

We already have heredity, exact reduct, finite nonempty expansion
fibres, and genuine strong amalgamation for the finite named
all-closed-component *maximal induced-trace* age.

Strong amalgamation does NOT imply that the new tag relations form
a free amalgam. In particular, a maximal extension of the native
free-amalgam witness may add new tags on mixed tuples. Thus the
free-amalgamation functional Ramsey theorem cannot simply be
instantiated with this age.

The following definition states the ACTUAL missing Ramsey-transfer
output: a finite member of the maximal-trace age, with one vertex
map from a finite Ramsey control C, FULL on EVERY displayed B-copy.
We prove that such a completion transfers the actual finite Ramsey
arrow, rather than merely giving an abstract class-level implication.

There is no assumption that the vertex map preserves all old
function fibres outside B-copies, or that all A-copies lift.
The central open obligation is to CONSTRUCT these copywise
completions from bounded local forbidden-family tests, with the
chosen bound depending on B and the Ramsey control, as in the
corrected 2019 multiamalgamation theorem.

The transfer itself works for any fixed functional language, but
the intended Ramsey CLASS theorem needs an appropriately ordered
maximal-trace age; the unordered age is not asserted to be Ramsey.
Nothing here resolves the printed arbitrary regular-family Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- The precise finite maximal-trace completion needed for the
last Ramsey step for one B and one finite control C. The map is
not required to be a full embedding on C, only on all B-copies.

A proof of this proposition must supply its witness, rather than
postulating the Ramsey conclusion. -/
def FiniteNamedTraceCopywiseCompletion
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VC : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC) : Prop :=
  ∃ (VD : Type)
    (D : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VD),
    IsFiniteNamedMaximalTrace Family D ∧
    ∃ (f : VC → VD),
      ∀ b : Structure.Embedding B C,
        ∃ bD : Structure.Embedding B D,
          ∀ x : VB, bD x = f (b x)

/-- The exact final Ramsey arrow follows from a genuine finite
B-copywise maximal-trace completion. The age membership is an
explicit output of the completion, not an assumption of the control.

The proof does NOT establish the existence of these completions. -/
theorem finiteNamedTraceArrow_of_copywiseCompletion
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VA VB VC : Type}
    {A : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VA}
    {B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB}
    {C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC}
    {κ : Type v} [Nonempty κ]
    (hArrow : Structure.Arrow A B C κ)
    (hCompletion : FiniteNamedTraceCopywiseCompletion Family B C) :
    ∃ (VD : Type) (_ : Finite VD)
      (D : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VD),
      IsFiniteNamedMaximalTrace Family D ∧
      Structure.Arrow A B D κ := by
  obtain ⟨VD, D, hD, f, hf⟩ := hCompletion
  exact ⟨VD, hD.1, D, hD,
    functionalArrow_of_BCopywiseCompletion hArrow hf⟩

/-- Any FULL embedding of the whole Ramsey control in a finite
maximal-trace age member supplies the stronger form of copywise
completion. This is useful as a sanity test, but it is generally
too restrictive for a local multiamalgamation construction. -/
theorem finiteNamedTraceCopywiseCompletion_of_embedding
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB VC VD : Type}
    {B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB}
    {C : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VC}
    {D : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VD}
    (hD : IsFiniteNamedMaximalTrace Family D)
    (e : Structure.Embedding C D) :
    FiniteNamedTraceCopywiseCompletion Family B C := by
  refine ⟨VD, D, hD, e, ?_⟩
  intro b
  exact ⟨e.comp b, by intro x; rfl⟩

end AllThoseRamseyClasses.Lifts
