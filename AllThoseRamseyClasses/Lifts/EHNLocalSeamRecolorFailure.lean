import AllThoseRamseyClasses.Lifts.EHNLexMinimalSeamCollisionWitness

/-!
# Track D: localize the precise EHN failure of a one-vertex seam split

Let f : Source → Target be an ACTUAL original native EHN map, and let
g differ from f only at ONE original source vertex a (recoloured
from one common-seam image to an UNUSED fresh target seam point).

If g is not EHN, then it has a genuinely LOCAL obstruction:

(1) a POSITIVE original source OLD relation tuple containing a is
    not preserved as a target positive tuple by g; OR
(2) a POSITIVE original native set-valued function incidence
    containing a as an INPUT or as its OUTPUT is not preserved; OR
(3) some ACTUAL full embedded irreducible native source test
    containing a cannot extend to ANY full target embedding whose
    vertex map is g on that test.

This classification uses the EXACT original weak-preservation and
irreducible FULL-test definition of IsEHNHomomorphismEmbedding.
It does not treat an arbitrary weak quotient as full, or require a
forbidden family, maximal lift, or source-map injectivity.

For a support-first/seam-collision-second minimal genuine forbidden
witness, the fresh unused seam split is NOT EHN, by the prior
counting contradiction. Consequently one of these three LOCAL
obstructions MUST occur at the selected source vertex a.

This is a useful diagnostic for a future collision-tolerant native
source extension/flip. It does not construct that extension, repair
the obstructing old relation/function/test, or complete Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- The exact LOCAL failure trichotomy for changing only ONE
original source vertex a of an ACTUAL EHN map. The changed map
need not be a weak homomorphism; the first two alternatives
identify positive old-relation or full native-function incidence
failures which MUST touch a, and the third gives a failed FULL
irreducible source test which MUST contain a.

The fresh target vertex is not required to be unused here;
locality follows solely from agreement of g with f away from a. -/
theorem ehn_oneVertexRecolor_failure_has_localNativeWitness
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (a : V) (fresh : UT)
    (hNoNewEHN : ¬ Source.IsEHNHomomorphismEmbedding Target
      (fun x : V => if x = a then fresh else f x)) :
    (∃ (R : L.RelSymbol)
        (xs : Fin (L.relArity R) → V),
      Source.rel R xs ∧
      ¬ Target.rel R
        ((fun x : V => if x = a then fresh else f x) ∘ xs) ∧
      ∃ i : Fin (L.relArity R), xs i = a) ∨
    (∃ (G : L.FuncSymbol)
        (xs : Fin (L.funcArity G) → V) (out : V),
      out ∈ Source.func G xs ∧
      (fun x : V => if x = a then fresh else f x) out ∉
        Target.func G
          ((fun x : V => if x = a then fresh else f x) ∘ xs) ∧
      (out = a ∨ ∃ i : Fin (L.funcArity G), xs i = a)) ∨
    (∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        (∃ x : X, e x = a) ∧
        ¬ ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x =
            (fun z : V => if z = a then fresh else f z) (e x)) := by
  classical
  let g : V → UT := fun x => if x = a then fresh else f x
  by_contra hNone
  have hRelations :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        Source.rel R xs → Target.rel R (g ∘ xs) := by
    intro R xs hSource
    by_contra hMissing
    have hTouches : ∃ i : Fin (L.relArity R), xs i = a := by
      by_contra hNoTouch
      have hEqArgs : g ∘ xs = f ∘ xs := by
        funext i
        have hi : xs i ≠ a := by
          intro heq
          exact hNoTouch ⟨i, heq⟩
        simp [g, hi]
      exact hMissing (by rw [hEqArgs]; exact hf.1.1 R xs hSource)
    exact hNone (Or.inl ⟨R, xs, hSource, hMissing, hTouches⟩)
  have hFunctions :
      ∀ (G : L.FuncSymbol) (xs : Fin (L.funcArity G) → V)
          (out : V),
        out ∈ Source.func G xs → g out ∈ Target.func G (g ∘ xs) := by
    intro G xs out hSource
    by_contra hMissing
    have hTouches :
        out = a ∨ ∃ i : Fin (L.funcArity G), xs i = a := by
      by_contra hNoTouch
      have hOutNe : out ≠ a := by
        intro hout
        exact hNoTouch (Or.inl hout)
      have hInputNe : ∀ i : Fin (L.funcArity G), xs i ≠ a := by
        intro i hi
        exact hNoTouch (Or.inr ⟨i, hi⟩)
      have hEqArgs : g ∘ xs = f ∘ xs := by
        funext i
        simp [g, hInputNe i]
      have hEqOut : g out = f out := by
        simp [g, hOutNe]
      have hTarget := hf.1.2 G xs out hSource
      exact hMissing (by rw [hEqOut, hEqArgs]; exact hTarget)
    exact hNone (Or.inr (Or.inl
      ⟨G, xs, out, hSource, hMissing, hTouches⟩))
  have hFullTests : ∀ {X : Type} (E : Structure L X),
      E.Irreducible →
      ∀ e : Structure.Embedding E Source,
        ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x = g (e x) := by
    intro X E hIrr e
    by_cases hTouches : ∃ x : X, e x = a
    · by_contra hNoEmbedding
      exact hNone (Or.inr (Or.inr
        ⟨X, E, hIrr, e, hTouches, hNoEmbedding⟩))
    · obtain ⟨ge, hge⟩ := hf.2 E hIrr e
      refine ⟨ge, ?_⟩
      intro x
      have hAway : e x ≠ a := by
        intro h
        exact hTouches ⟨x, h⟩
      simpa [g, hAway] using (hge x)
  exact hNoNewEHN ⟨⟨hRelations, hFunctions⟩, hFullTests⟩

/-- Exact LOCAL obstruction for a fresh unused seam vertex split
at an ORIGINAL lex-minimal finite forbidden EHN witness.

The old source F and its entire old native structure are unchanged.
Under an actual source collision a ≠ b at a seam image, a fresh
UNUSED target seam point and support-first/collision-second
minimality, the one-vertex recoloured map cannot be EHN. Hence
either a POSITIVE old relation containing a, a POSITIVE full
native function incidence incident with a, or a FULL embedded
irreducible source test containing a blocks that recolouring.

This pinpoints the missing OLD-language EHN-preservation step.
Maximal agreement of added canonical piece symbols alone is
not a hypothesis and does not eliminate any of these defects. -/
theorem lexMinimalForbiddenWitness_freshSeamSplit_has_localNativeFailure
    {F : ∀ {W : Type}, Structure L W → Prop}
    {UT : Type} {Target : Structure L UT}
    (LeftExclusive Seam : Set UT)
    (hDisjoint : Disjoint LeftExclusive Seam)
    (w : ForbiddenEHNWitness F Target)
    (hPrimary : ∀ v : ForbiddenEHNWitness F Target,
      w.sourceSupportCount LeftExclusive ≤
        v.sourceSupportCount LeftExclusive)
    (hSecondary : ∀ v : ForbiddenEHNWitness F Target,
      v.sourceSupportCount LeftExclusive =
        w.sourceSupportCount LeftExclusive →
      w.seamCollisionPairCount Seam ≤
        v.seamCollisionPairCount Seam)
    [DecidableEq w.Carrier]
    (a b : w.Carrier) (hab : a ≠ b)
    (hSame : w.toTarget a = w.toTarget b)
    (hSeam : w.toTarget a ∈ Seam)
    (fresh : UT) (hFreshSeam : fresh ∈ Seam)
    (hUnused : fresh ∉ Set.range w.toTarget) :
    (∃ (R : L.RelSymbol)
        (xs : Fin (L.relArity R) → w.Carrier),
      w.source.rel R xs ∧
      ¬ Target.rel R
        ((fun x : w.Carrier => if x = a then fresh
          else w.toTarget x) ∘ xs) ∧
      ∃ i : Fin (L.relArity R), xs i = a) ∨
    (∃ (G : L.FuncSymbol)
        (xs : Fin (L.funcArity G) → w.Carrier)
        (out : w.Carrier),
      out ∈ w.source.func G xs ∧
      (fun x : w.Carrier => if x = a then fresh
        else w.toTarget x) out ∉
        Target.func G
          ((fun x : w.Carrier => if x = a then fresh
            else w.toTarget x) ∘ xs) ∧
      (out = a ∨ ∃ i : Fin (L.funcArity G), xs i = a)) ∨
    (∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E w.source,
        (∃ x : X, e x = a) ∧
        ¬ ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x =
            (fun z : w.Carrier => if z = a then fresh
              else w.toTarget z) (e x)) := by
  have hNoNewEHN :
      ¬ w.source.IsEHNHomomorphismEmbedding Target
        (fun x : w.Carrier =>
          if x = a then fresh else w.toTarget x) := by
    intro hNew
    exact lexMinimalForbiddenWitness_no_freshSeamEHN_oneVertexSplit
      LeftExclusive Seam hDisjoint w hPrimary hSecondary
      a b hab hSame hSeam fresh hFreshSeam hUnused hNew
  exact ehn_oneVertexRecolor_failure_has_localNativeWitness
    w.source Target w.toTarget w.homEmbedding
    a fresh hNoNewEHN

/-- Exact LOCAL-TEST criterion for a proposed collision-repair
map g which agrees with a previously verified EHN map f at
EVERY original source vertex EXCEPT possibly one selected a.

The global new EHN condition is EQUIVALENT to exactly three
sets of local verification obligations:
* positive old relations containing a,
* positive native function incidences where a is an input
  or output, and
* full embeddings of irreducible original source tests
  containing a.

All positive incidences and full irreducible tests DISJOINT
from a are automatically handled by the PREVIOUS EHN map f.
This is an actual necessary AND sufficient local proof gate,
not merely the negative obstruction trichotomy above. No
assumption about a spare seam target point, finite forbidden
families or canonical lift is needed. -/
theorem ehn_map_changedAtOneVertex_iff_localNativeVerification
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f g : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (a : V)
    (hAway : ∀ x : V, x ≠ a → g x = f x) :
    Source.IsEHNHomomorphismEmbedding Target g ↔
      (∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        Source.rel R xs →
        (∃ i : Fin (L.relArity R), xs i = a) →
          Target.rel R (g ∘ xs)) ∧
      (∀ (G : L.FuncSymbol)
          (xs : Fin (L.funcArity G) → V) (out : V),
        out ∈ Source.func G xs →
        (out = a ∨ ∃ i : Fin (L.funcArity G), xs i = a) →
          g out ∈ Target.func G (g ∘ xs)) ∧
      (∀ {X : Type} (E : Structure L X),
        E.Irreducible →
        ∀ e : Structure.Embedding E Source,
          (∃ x : X, e x = a) →
          ∃ ge : Structure.Embedding E Target,
            ∀ x : X, ge x = g (e x)) := by
  classical
  constructor
  · intro hg
    refine ⟨?_, ?_, ?_⟩
    · intro R xs hSource _hTouches
      exact hg.1.1 R xs hSource
    · intro G xs out hSource _hTouches
      exact hg.1.2 G xs out hSource
    · intro X E hIr e _hTouches
      exact hg.2 E hIr e
  · rintro ⟨hLocalRelations, hLocalFunctions, hLocalTests⟩
    constructor
    · constructor
      · intro R xs hSource
        by_cases hTouches : ∃ i : Fin (L.relArity R), xs i = a
        · exact hLocalRelations R xs hSource hTouches
        · have hCoords : g ∘ xs = f ∘ xs := by
            funext i
            apply hAway
            intro heq
            exact hTouches ⟨i, heq⟩
          rw [hCoords]
          exact hf.1.1 R xs hSource
      · intro G xs out hSource
        by_cases hTouches :
            out = a ∨ ∃ i : Fin (L.funcArity G), xs i = a
        · exact hLocalFunctions G xs out hSource hTouches
        · have hOutNe : out ≠ a := by
            intro h
            exact hTouches (Or.inl h)
          have hInputNe : ∀ i : Fin (L.funcArity G), xs i ≠ a := by
            intro i h
            exact hTouches (Or.inr ⟨i, h⟩)
          have hCoords : g ∘ xs = f ∘ xs := by
            funext i
            exact hAway (xs i) (hInputNe i)
          have hValue : g out = f out :=
            hAway out hOutNe
          rw [hValue, hCoords]
          exact hf.1.2 G xs out hSource
    · intro X E hIr e
      by_cases hTouches : ∃ x : X, e x = a
      · exact hLocalTests E hIr e hTouches
      · obtain ⟨ge, hge⟩ := hf.2 E hIr e
        refine ⟨ge, ?_⟩
        intro x
        have hNe : e x ≠ a := by
          intro h
          exact hTouches ⟨x, h⟩
        exact (hge x).trans (hAway (e x) hNe).symm

end AllThoseRamseyClasses.Lifts
