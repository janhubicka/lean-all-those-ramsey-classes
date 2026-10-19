import AllThoseRamseyClasses.Lifts.GlobalConnectedForbiddenJEP

/-!
# Unconditional joint embedding for connected forbidden sources in positive arity

The general connected-source JEP theorem isolates a genuine issue for
nullary relations and functions: two native structures may not have
a common FULL empty-root substructure.

When EVERY native relation and function symbol has POSITIVE arity,
there is a canonical structure on Empty with no positive relations
and no function values. It fully embeds into EVERY native structure.
No nullary constraints or function-domain tokens are overlooked,
because no native symbol accepts an empty input tuple.

Thus connected nonempty forbidden sources in any such functional
language give native finite JEP directly by a free amalgam over the
literal empty carrier. Under regularity their actual original
global maximal induced-trace age also has JEP. The unconditional
strong amalgamation and Ramsey questions for REDUCIBLE sources
remain open.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Every native relation and every native function has a genuinely
positive arity. This prevents incompatible nullary old-language
information from obstructing a full common empty root. -/
def NativeLanguagePositiveArity (L : Language.{u}) : Prop :=
  (∀ R : L.RelSymbol, 0 < L.relArity R) ∧
  (∀ f : L.FuncSymbol, 0 < L.funcArity f)

/-- The literal empty native structure, with no old relation tuples
or old function values. It exists for any language, though it is
universally FULLY embeddable only under suitable arity conditions. -/
def nativeEmptyStructure (L : Language.{u}) : Structure L Empty where
  rel := fun _ _ => False
  func := fun _ _ => ∅

/-- In a positive-arity native language the empty structure is a
FULL functional substructure of EVERY old structure. In particular
there are no hidden nullary functions whose fibres must be matched. -/
def nativeEmptyFullEmbedding
    (L : Language.{u}) (hArity : NativeLanguagePositiveArity L)
    {V : Type} (A : Structure L V) :
    Structure.Embedding (nativeEmptyStructure L) A where
  toFun := Empty.elim
  injective := by
    intro x
    exact isEmptyElim x
  map_rel_iff := by
    intro R xs
    exact isEmptyElim (xs ⟨0, hArity.1 R⟩)
  map_func := by
    intro f xs
    exact isEmptyElim (xs ⟨0, hArity.2 f⟩)

/-- The FULL common empty-root condition required in the connected
JEP theorem is automatic for all allowed classes, without requiring
even one forbidden-family hypothesis, if every old symbol has
positive arity. -/
theorem nativeCommonEmptyRoots_of_positiveArity
    (L : Language.{u}) (hArity : NativeLanguagePositiveArity L)
    (K : ∀ {W : Type}, Structure L W → Prop) :
    GlobalNativeCommonEmptyRoots K := by
  intro UA UB A B _ _ _ _
  exact ⟨Empty, inferInstance, nativeEmptyStructure L,
    nativeEmptyFullEmbedding L hArity A,
    nativeEmptyFullEmbedding L hArity B, True.intro⟩

/-- For ANY family of finite, nonempty, Gaifman-connected EHN
forbidden native structures, the forbidden-free class has FULL
finite JEP in every positive-arity native functional language.
The constructed joint target is the ACTUAL empty-root free amalgam. -/
theorem globalNativeFiniteJEP_connected_positiveArity
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F) :
    GlobalNativeFiniteJEP
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) := by
  exact globalNativeFiniteJEP_connected_of_emptyRoots F hConnected
    (nativeCommonEmptyRoots_of_positiveArity L hArity
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A))

/-- Original regular global maximal-trace lift of ANY family of
finite connected nonempty EHN forbidden sources has full JEP,
without an additional native-JEP premise, when the old functional
language has no nullary symbols. This does NOT use the unresolved
general shadow strong-amalgamation lemma. -/
theorem globalMaximalTraceAge_JEP_connected_positiveArity
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {VY VZ : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Y)
    (hZ : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Z) :
    ∃ (VT : Type) (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {V : Type} (A : Structure L V) =>
          AvoidsGlobalFunctionalEHN F A) T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T), True := by
  exact globalFiniteMaximalTraceAge_JEP_of_nativeJEP
    F (fun {V : Type} (A : Structure L V) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular
    (globalNativeFiniteJEP_connected_positiveArity F hArity hConnected)
    Y Z hY hZ

end AllThoseRamseyClasses.Lifts
