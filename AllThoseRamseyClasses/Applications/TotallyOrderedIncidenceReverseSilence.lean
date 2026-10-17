import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceTwoWayCoordinates
import PartiteConstruction.Structure.FreeAmalgam

/-!
# Empty reverse-coordinate fibres outside their generating symbol sort

The canonical two-way incidence lift has reverse operations G_(r,i)
with singleton output only at a generated tag of symbol r.
On every ORIGINAL vertex and every tag of a DIFFERENT symbol, the
reverse output is exactly the empty set.

A Ramsey witness for the auxiliary incidence class must retain
these exact empty fibres. Otherwise the canonical lift of an
original A-copy may fail to reflect reverse functions, even though
the positive incidence tags and their original roots are correct.

These two local universal conditions are verified for canonical
two-way lifts, reflected by FULL functional embeddings and preserved
by genuine FULL functional free amalgamation. Orphan tags of their
own symbol are intentionally allowed arbitrary reverse fibres.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v

/-- Reverse G_(r,i) is empty on old vertices and on tags whose
different symbol is s ≠ r. It is not required to be defined on
orphan tags of the correct symbol. -/
structure ReverseCoordinateSilence
    {L : RelLanguage.{u}} {V : Type v}
    (C : Structure (twoWayIncidenceLanguage L) V) : Prop where
  on_old :
    ∀ (r : L.Symbol) (i : Fin (L.arity r)) (x : V),
      C.rel .old ![x] →
      C.func (.inr ⟨r,i⟩) ![x] = ∅
  on_wrong_symbol :
    ∀ (r s : L.Symbol) (h : r ≠ s)
      (i : Fin (L.arity s)) (x : V),
      C.rel (.newSymbol r) ![x] →
      C.func (.inr ⟨s,i⟩) ![x] = ∅

/-- Canonical two-way incidence lifts have no reverse output on
old inputs or wrong-symbol tags. All relation arities, including
the empty reverse-coordinate family for nullary symbols, work. -/
theorem canonical_reverseCoordinateSilence
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {V : Type v}
    (A : TotalOrderData L V) :
    ReverseCoordinateSilence (canonicalTwoWayIncidence A) := by
  classical
  refine ⟨?_, ?_⟩
  · intro r i x hOld
    change isOriginalVertex A x at hOld
    change reverseCoordinateFibre A r i x = ∅
    cases x with
    | inl a =>
        ext y
        constructor
        · rintro ⟨t, ht, hTag, hy⟩
          cases hTag
        · intro hy
          cases hy
    | inr a => exact False.elim hOld
  · intro r s hNe i x hSymbol
    change hasIncidenceSymbol A r x at hSymbol
    change reverseCoordinateFibre A s i x = ∅
    cases x with
    | inl a => exact False.elim hSymbol
    | inr tag =>
        rcases tag with ⟨q, ⟨t, ht⟩⟩
        change q = r at hSymbol
        subst q
        ext y
        constructor
        · rintro ⟨t', ht', hTag, hy⟩
          have hSigma :
              (⟨r, ⟨t, ht⟩⟩ :
                Sigma fun z : L.Symbol =>
                  {a : Fin (L.arity z) → V // A.base.rel z a}) =
              ⟨s, ⟨t', ht'⟩⟩ :=
            Sum.inr.inj (by simpa only [positiveTag] using hTag)
          exact (hNe (congrArg Sigma.fst hSigma)).elim
        · intro hy
          cases hy

/-- An empty target function fibre reflects to the source under
any FULL embedding, by equality of the image of the source fibre. -/
private theorem empty_fibre_reflect
    {M : Language.{u}} {U V : Type v}
    {A : Structure M U} {B : Structure M V}
    (e : Structure.Embedding A B)
    (F : M.FuncSymbol) (t : Fin (M.funcArity F) → U)
    (hB : B.func F (e ∘ t) = ∅) :
    A.func F t = ∅ := by
  ext x
  constructor
  · intro hx
    have he : e x ∈ e '' A.func F t := ⟨x, hx, rfl⟩
    change e x ∈ imageSet e (A.func F t) at he
    rw [e.map_func F t, hB] at he
    cases he
  · intro hx
    cases hx

/-- Exact reverse silence is reflected by all FULL embeddings. -/
theorem ReverseCoordinateSilence.of_embedding
    {L : RelLanguage.{u}} {U V : Type v}
    {A : Structure (twoWayIncidenceLanguage L) U}
    {B : Structure (twoWayIncidenceLanguage L) V}
    (hB : ReverseCoordinateSilence B)
    (e : Structure.Embedding A B) :
    ReverseCoordinateSilence A := by
  refine ⟨?_, ?_⟩
  · intro r i x hOld
    have ht : (e ∘ ![x]) = ![e x] := by
      funext j
      fin_cases j
      rfl
    have hBrel : B.rel .old ![e x] := by
      have h := e.map_rel_iff (.old) ![x]
      rw [ht] at h
      exact h.mpr hOld
    apply empty_fibre_reflect e (.inr ⟨r,i⟩) ![x]
    rw [ht]
    exact hB.on_old r i (e x) hBrel
  · intro r s hNe i x hNew
    have ht : (e ∘ ![x]) = ![e x] := by
      funext j
      fin_cases j
      rfl
    have hBrel : B.rel (.newSymbol r) ![e x] := by
      have h := e.map_rel_iff (.newSymbol r) ![x]
      rw [ht] at h
      exact h.mpr hNew
    apply empty_fibre_reflect e (.inr ⟨s,i⟩) ![x]
    rw [ht]
    exact hB.on_wrong_symbol r s hNe i (e x) hBrel

/-- The complete image of an empty source function fibre is
empty, exactly; no weak homomorphism is sufficient here. -/
private theorem empty_fibre_push
    {M : Language.{u}} {U V : Type v}
    {A : Structure M U} {B : Structure M V}
    (e : Structure.Embedding A B)
    (F : M.FuncSymbol) (t : Fin (M.funcArity F) → U)
    (hA : A.func F t = ∅) :
    B.func F (e ∘ t) = ∅ := by
  rw [← e.map_func F t, hA]
  rfl

/-- Reverse-coordinate silence remains valid under genuine FULL
functional free amalgamation. Every vertex comes from a side;
its unary symbol is reflected on that side and its reverse output
set is exactly the embedded image of the side's empty set. -/
theorem ReverseCoordinateSilence.free_amalgam
    {L : RelLanguage.{u}}
    {H E F W : Type v}
    {D : Structure (twoWayIncidenceLanguage L) H}
    {A : Structure (twoWayIncidenceLanguage L) E}
    {B : Structure (twoWayIncidenceLanguage L) F}
    {C : Structure (twoWayIncidenceLanguage L) W}
    {sA : Structure.Embedding D A}
    {sB : Structure.Embedding D B}
    {iA : Structure.Embedding A C}
    {iB : Structure.Embedding B C}
    (hfree : IsFreeAmalgam sA sB iA iB)
    (hA : ReverseCoordinateSilence A)
    (hB : ReverseCoordinateSilence B) :
    ReverseCoordinateSilence C := by
  refine ⟨?_, ?_⟩
  · intro r i x hOld
    rcases hfree.covers x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ht : (iA ∘ ![a]) = ![iA a] := by
        funext j
        fin_cases j
        rfl
      have hAOld : A.rel .old ![a] := by
        have h := iA.map_rel_iff (.old) ![a]
        rw [ht] at h
        exact h.mp hOld
      rw [← ht]
      exact empty_fibre_push iA (.inr ⟨r,i⟩) ![a]
        (hA.on_old r i a hAOld)
    · have ht : (iB ∘ ![b]) = ![iB b] := by
        funext j
        fin_cases j
        rfl
      have hBOld : B.rel .old ![b] := by
        have h := iB.map_rel_iff (.old) ![b]
        rw [ht] at h
        exact h.mp hOld
      rw [← ht]
      exact empty_fibre_push iB (.inr ⟨r,i⟩) ![b]
        (hB.on_old r i b hBOld)
  · intro r s hNe i x hNew
    rcases hfree.covers x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have ht : (iA ∘ ![a]) = ![iA a] := by
        funext j
        fin_cases j
        rfl
      have hANew : A.rel (.newSymbol r) ![a] := by
        have h := iA.map_rel_iff (.newSymbol r) ![a]
        rw [ht] at h
        exact h.mp hNew
      rw [← ht]
      exact empty_fibre_push iA (.inr ⟨s,i⟩) ![a]
        (hA.on_wrong_symbol r s hNe i a hANew)
    · have ht : (iB ∘ ![b]) = ![iB b] := by
        funext j
        fin_cases j
        rfl
      have hBNew : B.rel (.newSymbol r) ![b] := by
        have h := iB.map_rel_iff (.newSymbol r) ![b]
        rw [ht] at h
        exact h.mp hNew
      rw [← ht]
      exact empty_fibre_push iB (.inr ⟨s,i⟩) ![b]
        (hB.on_wrong_symbol r s hNe i b hBNew)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
