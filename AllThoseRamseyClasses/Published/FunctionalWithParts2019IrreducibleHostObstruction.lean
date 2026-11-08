import AllThoseRamseyClasses.Published.FunctionalWithParts2019NativeKClosedHeredity

/-!
# Appendix Track B adversarial regression: canonical K_H need not be irreducible

An assembled 2019 class-transfer theorem currently assumes both
  (1) every canonical tagged genuine H_K object belongs to R, and
  (2) every R object is an ORDINARY irreducible relational structure.

These assumptions jointly force every K_H member to be irreducible.
This is FALSE in general for the faithful H_K image of an arbitrary
native free-amalgamation class K, even when K is the simplest possible
class of ALL structures in the EMPTY original relation/function language.

Take two isolated vertices and one vertex part. The faithful source
retains both vertices, and its canonical complete-mask/root-tagged
language has ONLY unary part relations: there are no function input
patterns, no domain masks, no output masks, and no fresh root tags.
Its tagged K_H image is therefore NOT irreducible.

This regression deliberately proves an actual finite counterexample,
rather than silently choosing an irreducible Ramsey ambient host R
that cannot possibly contain this K_H. It does NOT refute the
conditional theorem when all its hypotheses happen to hold, nor
solve the independent ambient-relative weak-test local completion.

No frozen survey prose, prior author TODO, or dependency pin is changed.
-/

namespace AllThoseRamseyClasses.Published.TrackBIrreducibleHostObstruction

open StructuralRamsey
open StructuralRamsey.Structure
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

/-- The finite empty original relation/function language. -/
def emptyLanguage : Language.{0} where
  RelSymbol := Empty
  FuncSymbol := Empty
  relArity := Empty.elim
  funcArity := Empty.elim

/-- The native class of ALL structures in the empty language. -/
def allNativeClass :
    Structure.StructureClass.{0,0} (L := emptyLanguage) :=
  fun {_} _ => True

/-- All native empty-language structures form a hereditary free
amalgamation class: both class axioms are literally trivial. -/
theorem allNativeClass_freeAmalgamation :
    Structure.FreeAmalgamationClass allNativeClass := by
  constructor
  · intros
    trivial
  · intros
    trivial

/-- Two distinct native vertices, both in the unique part and
with no primitive relation or function symbols at all. -/
def twoIsolatedNative :
    FunctionalPartite.System emptyLanguage PUnit (Fin 2) where
  toStructure := {
    rel := fun R => Empty.elim R
    func := fun F => Empty.elim F
  }
  part := fun _ => PUnit.unit
  relTransversal := by
    intro R
    exact Empty.elim R
  funcTransversal := by
    intro F
    exact Empty.elim F

/-- Genuine H_K-members are exactly faithful Option(Set) images
of native part-labelled objects in the all-native class. -/
def faithfulH :
    GenuinePartite2019Class.{0,0,0}
      (L := emptyLanguage) (Parts := PUnit) :=
  nativeKFaithfulGenuinePartiteH2019
    (Parts := PUnit) allNativeClass

/-- The literal canonical two-point tagged image, without adding
an order, extra edges or fictitious function-domain incidences. -/
def twoIsolatedTagged :
    RelStructure
      ((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit)
      (Fin 2) :=
  wholeMaskTagExpansion
    (withPartsWholeMaskOld
      twoIsolatedNative.toStructure.toNonemptyPartial
      twoIsolatedNative.part)

/-- This real, two-point canonical image belongs to K_H. -/
theorem twoIsolatedTagged_mem :
    canonicalGenuineTagged2019Class faithfulH twoIsolatedTagged := by
  change canonicalGenuineTagged2019Class faithfulH
    (wholeMaskTagExpansion
      (withPartsWholeMaskOld
        twoIsolatedNative.toStructure.toNonemptyPartial
        twoIsolatedNative.part))
  apply canonicalGenuineTagged2019Class_mem faithfulH
    twoIsolatedNative.toStructure.toNonemptyPartial
    twoIsolatedNative.part
  · exact ⟨twoIsolatedNative, trivial, rfl, rfl⟩
  · exact twoIsolatedNative.toNonemptyPartial_fibreTransversal

/-- With no ORIGINAL function symbols, all possible whole-mask
domain/output patterns and all positive-output closure tags are
empty types. The only remaining tagged symbols are unary part
predicates. -/
theorem allTaggedSymbolsUnary
    (R : ((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit).Symbol) :
    ((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit).arity R = 1 := by
  cases R with
  | inl old =>
      cases old with
      | inl orig =>
          cases orig with
          | inl oldR =>
              exact Empty.elim oldR.down
          | inr _ =>
              rfl
      | inr mask =>
          cases mask with
          | inl p =>
              exact Empty.elim p.1.symbol.down
          | inr p =>
              exact Empty.elim p.1.symbol.down
  | inr pattern =>
      exact Empty.elim pattern.input.symbol.down

/-- Two different isolated vertices cannot be jointly covered
by any relation tuple of arity one. The canonical two-vertex
K_H member therefore fails ORDINARY irreducibility. -/
theorem twoIsolatedTagged_not_irreducible :
    ¬ twoIsolatedTagged.Irreducible := by
  intro hIrred
  have hDistinct : (0 : Fin 2) ≠ 1 := by decide
  obtain ⟨R, xs, i, j, _hRel, hxi, hxj⟩ :=
    hIrred (x := (0 : Fin 2)) (y := (1 : Fin 2)) hDistinct
  have hSubsingleton :
      Subsingleton
        (Fin (((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit).arity R)) := by
    rw [allTaggedSymbolsUnary R]
    infer_instance
  have hij : i = j := Subsingleton.elim i j
  apply hDistinct
  calc
    (0 : Fin 2) = xs i := hxi.symm
    _ = xs j := congrArg xs hij
    _ = (1 : Fin 2) := hxj

/-- There exists NO relational class R containing EVERY canonical
tagged member of this faithful native K that also consists
entirely of ordinary irreducible objects. This holds whether or
not the hypothetical R is Ramsey: the class inclusion and
irreducibility requirements are already inconsistent.

In particular the stronger native K free-amalgamation axioms alone
do NOT furnish such a Ramsey host for the assembled 2019 theorem. -/
theorem no_universally_irreducible_host
    (R : StructureClass.{0,0}
      (L := (emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit))
    (hSub : ∀ {X : Type}
      (E : RelStructure
        ((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit) X),
      canonicalGenuineTagged2019Class faithfulH E → R E)
    (hRIrred : ∀ {X : Type}
      (E : RelStructure
        ((emptyLanguage.withParts PUnit).wholeMaskTagLanguage PUnit) X),
      R E → E.Irreducible) : False :=
  twoIsolatedTagged_not_irreducible
    (hRIrred twoIsolatedTagged
      (hSub twoIsolatedTagged twoIsolatedTagged_mem))

end AllThoseRamseyClasses.Published.TrackBIrreducibleHostObstruction
