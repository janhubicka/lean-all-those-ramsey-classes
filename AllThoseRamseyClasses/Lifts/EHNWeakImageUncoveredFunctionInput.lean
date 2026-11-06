import AllThoseRamseyClasses.Lifts.EHNWeakSideFullReflectionDefect
import AllThoseRamseyClasses.Lifts.EHNInputTestCoverageClosedRange

/-!
# Track D: a function-fibre defect identifies an uncovered original input tuple

The exact original EHN irreducible-test clause is LOCAL.
Given an original source function-input tuple xs contained in
one FULL irreducible source test, all target function values at
f ∘ xs must be images of actual source function values.

Suppose a bad FULL irreducible test E of the generated weak
quotient Q is weakly factored into a full target side. If the
side has an extra function value at some E-input tuple, then
NO original-source tuple in the appropriate quotient-coordinate
fibre is covered by any full irreducible test of the original
source. Otherwise the original EHN map would lift that value,
the generated quotient would contain it, and the full embedding
E ↪ Q would reflect it into E, contradiction.

This improves the previously conditional global function-input
coverage reduction: under the printed assumptions ALONE, a bad
quotient test entails EITHER an extra positive relation in one
side OR an extra function value whose source input coordinates
are entirely UNPROTECTED by source irreducible tests.

It does not assert that maximal-lift compatibility excludes
such a source tuple. That remains the open root/collision gate.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A SINGLE source native function-input tuple is contained in
some genuinely FULL irreducible source test. This is the local
counterpart of the global `FunctionInputTuplesCoveredByIrreducibleTests`
predicate, with no assumption on any OTHER input tuple. -/
def FunctionInputCoveredByFullIrreducibleTest
    {V : Type} (A : Structure L V)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) : Prop :=
  ∃ (U : Type) (E : Structure L U),
    E.Irreducible ∧
    ∃ (e : Structure.Embedding E A)
      (ys : Fin (L.funcArity F) → U),
      ∀ i, e (ys i) = xs i

/-- A local full irreducible input test suffices to lift EACH
target native function output on that particular input tuple
back into a positive original-source function incidence.
No global input cover or closed target range is required. -/
theorem ehn_localFunctionInputCover_liftsTargetOutput
    {V W : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V)
    (hCovered : FunctionInputCoveredByFullIrreducibleTest A F xs)
    (z : W) (hz : z ∈ B.func F (f ∘ xs)) :
    z ∈ imageSet f (A.func F xs) := by
  classical
  obtain ⟨U, E, hIrr, e, ys, hys⟩ := hCovered
  obtain ⟨g, hg⟩ := hf.2 E hIrr e
  have hArgs : g ∘ ys = f ∘ xs := by
    funext i
    calc
      g (ys i) = f (e (ys i)) := hg (ys i)
      _ = f (xs i) := congrArg f (hys i)
  have hTarget : z ∈ B.func F (g ∘ ys) := by
    rw [hArgs]
    exact hz
  have hInE : z ∈ imageSet g (E.func F ys) := by
    rw [g.map_func F ys]
    exact hTarget
  obtain ⟨v, hv, hgv⟩ := hInE
  have hEImage : e v ∈ imageSet e (E.func F ys) :=
    ⟨v, hv, rfl⟩
  rw [e.map_func F ys] at hEImage
  have hSourceArgs : e ∘ ys = xs := by
    funext i
    exact hys i
  rw [hSourceArgs] at hEImage
  exact ⟨e v, hEImage, (hg v).symm.trans hgv⟩

/-- If a side-local full quotient test is missing a target
function value, then EVERY source input tuple whose coordinates
map to that test tuple lacks a full irreducible source test.

The true source-generated weak image is used, so an original
positive function incidence would generate the target value
inside Q; fullness of E ↪ Q would then force it into E. -/
theorem weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
    {V W U US : Type}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (E : Structure L U)
    (e : Structure.Embedding E (Structure.weakImage A B f))
    (Side : Structure L US)
    (j : Structure.Embedding Side B)
    (g : U → US)
    (hCoords : ∀ x : U, j (g x) = (e x).1)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → U)
    (z : US)
    (hSideValue : z ∈ Side.func F (g ∘ xs))
    (hNotSourceTestValue : z ∉ imageSet g (E.func F xs))
    (ys : Fin (L.funcArity F) → V)
    (hInputCoords : ∀ i, f (ys i) = (e (xs i)).1) :
    ¬ FunctionInputCoveredByFullIrreducibleTest A F ys := by
  intro hCovered
  have hSideB : j z ∈ B.func F (j ∘ (g ∘ xs)) := by
    have hImg : j z ∈ imageSet j (Side.func F (g ∘ xs)) :=
      ⟨z, hSideValue, rfl⟩
    rw [j.map_func F (g ∘ xs)] at hImg
    exact hImg
  have hArgs : f ∘ ys = j ∘ (g ∘ xs) := by
    funext i
    calc
      f (ys i) = (e (xs i)).1 := hInputCoords i
      _ = j (g (xs i)) := (hCoords (xs i)).symm
  have hTarget : j z ∈ B.func F (f ∘ ys) := by
    rw [hArgs]
    exact hSideB
  obtain ⟨v, hv, hvz⟩ :
      ∃ v : V, v ∈ A.func F ys ∧ f v = j z :=
    ehn_localFunctionInputCover_liftsTargetOutput
      A B f hf F ys hCovered (j z) hTarget
  let qv : Set.range f := ⟨f v, ⟨v, rfl⟩⟩
  have hQuotient :
      qv ∈ (Structure.weakImage A B f).func F (e ∘ xs) := by
    change ∃ (args : Fin (L.funcArity F) → V) (out : V),
      out ∈ A.func F args ∧
      (∀ i, (e ∘ xs) i =
        (⟨f (args i), ⟨args i, rfl⟩⟩ : Set.range f)) ∧
      qv = ⟨f out, ⟨out, rfl⟩⟩
    refine ⟨ys, v, hv, ?_, rfl⟩
    intro i
    exact Subtype.ext (hInputCoords i).symm
  have hEImage : qv ∈ imageSet e (E.func F xs) := by
    rw [e.map_func F xs]
    exact hQuotient
  obtain ⟨u, hu, hue⟩ := hEImage
  have hgu : g u = z := by
    apply j.injective
    calc
      j (g u) = (e u).1 := hCoords u
      _ = qv.1 := congrArg Subtype.val hue
      _ = j z := hvz
  exact hNotSourceTestValue ⟨u, hu, hgu⟩

/-- A bad FULL quotient test in an actual full target free
amalgam therefore yields a SIDE relation surplus, OR a
function-fibre surplus whose input coordinates have NO
irreducibly covered original source preimage tuple.

Unlike the global function-input-cover theorem, this
unconditional structural dichotomy does not assume an
additional source cover predicate. It preserves the exact
forbidden quotient copy, its irreducible test, source
nonlifting certificate and genuine side-map coordinates. -/
theorem badForbiddenWeakImageTest_hasRelationOrUncoveredFunctionInput
    (F : ∀ {X : Type}, Structure L X → Prop)
    {UX UA UB UT : Type}
    (Root : Structure L UX)
    (Left : Structure L UA) (Right : Structure L UB)
    (Target : Structure L UT)
    (sL : Structure.Embedding Root Left)
    (sR : Structure.Embedding Root Right)
    (jL : Structure.Embedding Left Target)
    (jR : Structure.Embedding Right Target)
    (hFree : Structure.IsFreeAmalgam sL sR jL jR)
    (w : ForbiddenEHNWitness F Target)
    (hBad : HasForbiddenWeakImageBadIrreducibleTest F Target w) :
    ∃ (Z : Type) (P : Structure L Z),
      F P ∧
      ∃ (e : Structure.Embedding P
        (Structure.weakImage w.source Target w.toTarget))
        (U : Type) (E : Structure L U),
        E.Irreducible ∧
        ∃ (h : Structure.Embedding E P),
          (¬ ∃ k : Structure.Embedding E w.source,
            ∀ x : U,
              Structure.weakImage.quotientMap
                (f := w.toTarget) (k x) = e (h x)) ∧
          ((∃ (g : U → UA),
             E.IsWeakHomomorphism Left g ∧
             (∀ x : U, jL (g x) = (e (h x)).1) ∧
             ((∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Left.rel R (g ∘ xs) ∧ ¬ E.rel R xs) ∨
              (∃ (F0 : L.FuncSymbol)
                  (xs : Fin (L.funcArity F0) → U) (z : UA),
                z ∈ Left.func F0 (g ∘ xs) ∧
                z ∉ imageSet g (E.func F0 xs) ∧
                ∀ ys : Fin (L.funcArity F0) → w.Carrier,
                  (∀ i, w.toTarget (ys i) = (e (h (xs i))).1) →
                  ¬ FunctionInputCoveredByFullIrreducibleTest
                    w.source F0 ys))) ∨
           (∃ (g : U → UB),
             E.IsWeakHomomorphism Right g ∧
             (∀ x : U, jR (g x) = (e (h x)).1) ∧
             ((∃ (R : L.RelSymbol) (xs : Fin (L.relArity R) → U),
               Right.rel R (g ∘ xs) ∧ ¬ E.rel R xs) ∨
              (∃ (F0 : L.FuncSymbol)
                  (xs : Fin (L.funcArity F0) → U) (z : UB),
                z ∈ Right.func F0 (g ∘ xs) ∧
                z ∉ imageSet g (E.func F0 xs) ∧
                ∀ ys : Fin (L.funcArity F0) → w.Carrier,
                  (∀ i, w.toTarget (ys i) = (e (h (xs i))).1) →
                  ¬ FunctionInputCoveredByFullIrreducibleTest
                    w.source F0 ys)))) := by
  obtain ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, hSide⟩ :=
    badForbiddenWeakImageTest_hasSideReflectionDefect
      F Root Left Right Target sL sR jL jR hFree w hBad
  refine ⟨Z, P, hP, e, U, E, hIrr, h, hNoLift, ?_⟩
  rcases hSide with
      ⟨g, hgWeak, hgCoords, hSurplus⟩ |
      ⟨g, hgWeak, hgCoords, hSurplus⟩
  · left
    refine ⟨g, hgWeak, hgCoords, ?_⟩
    rcases hSurplus with hRelation | hFunction
    · exact Or.inl hRelation
    · obtain ⟨F0, xs, z, hSideValue, hMissing⟩ := hFunction
      refine Or.inr ⟨F0, xs, z, hSideValue, hMissing, ?_⟩
      intro ys hInputCoords
      exact weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
        w.source Target w.toTarget w.homEmbedding
        E (e.comp h) Left jL g hgCoords
        F0 xs z hSideValue hMissing ys hInputCoords
  · right
    refine ⟨g, hgWeak, hgCoords, ?_⟩
    rcases hSurplus with hRelation | hFunction
    · exact Or.inl hRelation
    · obtain ⟨F0, xs, z, hSideValue, hMissing⟩ := hFunction
      refine Or.inr ⟨F0, xs, z, hSideValue, hMissing, ?_⟩
      intro ys hInputCoords
      exact weakImageFullTest_sideExtraFunction_forcesUncoveredSourceInput
        w.source Target w.toTarget w.homEmbedding
        E (e.comp h) Right jR g hgCoords
        F0 xs z hSideValue hMissing ys hInputCoords

end AllThoseRamseyClasses.Lifts
