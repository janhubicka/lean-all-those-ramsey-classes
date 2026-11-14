import AllThoseRamseyClasses.Lifts.EHNLocalSeamRecolorFailure

/-!
# Track D: exact EHN verification after changing an arbitrary source vertex set

Let f : V → UT be an ACTUAL original native EHN map and let g agree
with f away from an arbitrary source set S. This module isolates the
three exact ORIGINAL-language checks needed for g to remain EHN:
positive old relations meeting S, positive full set-valued native
function incidences meeting S (through an input OR output), and FULL
target embeddings of original irreducible source tests meeting S.

Neither finiteness nor closedness of S is needed for locality. In
particular this can be applied to a finite seam hull, without
pretending that checks at one generator cover its entire closure.

This is a same-source map-recolouring theorem, NOT a justification for
replacing the carrier/functional structure of a selected geometric
piece, a source-image quotient, or the unrestricted 2019 Claim 2.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Exact NECESSARY AND SUFFICIENT native EHN verification gate when a
map of the SAME original source is changed only on an arbitrary S.

Every original positive old relation or native function incidence
whose participating source vertices ALL avoid S is transported by
the previous verified EHN map. Likewise an irreducible full source
test disjoint from S keeps its previous FULL target embedding.

The positive function obligation explicitly includes its OUTPUT
vertex: checking only changed input coordinates is insufficient
for set-valued native functions. -/
theorem ehn_map_changedOnSet_iff_localNativeVerification
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f g : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (S : Set V)
    (hAway : ∀ x : V, x ∉ S → g x = f x) :
    Source.IsEHNHomomorphismEmbedding Target g ↔
      (∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        Source.rel R xs →
        (∃ i : Fin (L.relArity R), xs i ∈ S) →
          Target.rel R (g ∘ xs)) ∧
      (∀ (G : L.FuncSymbol)
          (xs : Fin (L.funcArity G) → V) (out : V),
        out ∈ Source.func G xs →
        (out ∈ S ∨ ∃ i : Fin (L.funcArity G), xs i ∈ S) →
          g out ∈ Target.func G (g ∘ xs)) ∧
      (∀ {X : Type} (E : Structure L X),
        E.Irreducible →
        ∀ e : Structure.Embedding E Source,
          (∃ x : X, e x ∈ S) →
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
        by_cases hTouches : ∃ i : Fin (L.relArity R), xs i ∈ S
        · exact hLocalRelations R xs hSource hTouches
        · have hCoords : g ∘ xs = f ∘ xs := by
            funext i
            apply hAway
            intro hi
            exact hTouches ⟨i, hi⟩
          rw [hCoords]
          exact hf.1.1 R xs hSource
      · intro G xs out hSource
        by_cases hTouches :
            out ∈ S ∨ ∃ i : Fin (L.funcArity G), xs i ∈ S
        · exact hLocalFunctions G xs out hSource hTouches
        · have hOutAway : out ∉ S := by
            intro hout
            exact hTouches (Or.inl hout)
          have hInputsAway :
              ∀ i : Fin (L.funcArity G), xs i ∉ S := by
            intro i hi
            exact hTouches (Or.inr ⟨i, hi⟩)
          have hCoords : g ∘ xs = f ∘ xs := by
            funext i
            exact hAway (xs i) (hInputsAway i)
          have hValue : g out = f out :=
            hAway out hOutAway
          rw [hValue, hCoords]
          exact hf.1.2 G xs out hSource
    · intro X E hIr e
      by_cases hTouches : ∃ x : X, e x ∈ S
      · exact hLocalTests E hIr e hTouches
      · obtain ⟨ge, hge⟩ := hf.2 E hIr e
        refine ⟨ge, ?_⟩
        intro x
        have hOutside : e x ∉ S := by
          intro hx
          exact hTouches ⟨x, hx⟩
        exact (hge x).trans (hAway (e x) hOutside).symm

/-- Every failure of a candidate SAME-SOURCE EHN recolouring is
witnessed in the ORIGINAL source by a positive relation meeting the
changed set S, a positive native function incidence meeting S in an
input OR output, or an original irreducible FULL source test meeting
S whose prescribed target images do not admit a full embedding.

There are no hidden global failure classes outside S. No claim is
made that a replacement satisfying all three conditions exists. -/
theorem ehn_map_changedOnSet_failure_has_localNativeWitness
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f g : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f)
    (S : Set V)
    (hAway : ∀ x : V, x ∉ S → g x = f x)
    (hNoNewEHN : ¬ Source.IsEHNHomomorphismEmbedding Target g) :
    (∃ (R : L.RelSymbol)
        (xs : Fin (L.relArity R) → V),
      Source.rel R xs ∧
      ¬ Target.rel R (g ∘ xs) ∧
      ∃ i : Fin (L.relArity R), xs i ∈ S) ∨
    (∃ (G : L.FuncSymbol)
        (xs : Fin (L.funcArity G) → V) (out : V),
      out ∈ Source.func G xs ∧
      g out ∉ Target.func G (g ∘ xs) ∧
      (out ∈ S ∨ ∃ i : Fin (L.funcArity G), xs i ∈ S)) ∨
    (∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        (∃ x : X, e x ∈ S) ∧
        ¬ ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x = g (e x)) := by
  classical
  by_contra hNone
  have hLocalRelations :
      ∀ (R : L.RelSymbol) (xs : Fin (L.relArity R) → V),
        Source.rel R xs →
        (∃ i : Fin (L.relArity R), xs i ∈ S) →
          Target.rel R (g ∘ xs) := by
    intro R xs hSource hTouches
    by_contra hMissing
    exact hNone (Or.inl
      ⟨R, xs, hSource, hMissing, hTouches⟩)
  have hLocalFunctions :
      ∀ (G : L.FuncSymbol)
          (xs : Fin (L.funcArity G) → V) (out : V),
        out ∈ Source.func G xs →
        (out ∈ S ∨ ∃ i : Fin (L.funcArity G), xs i ∈ S) →
          g out ∈ Target.func G (g ∘ xs) := by
    intro G xs out hSource hTouches
    by_contra hMissing
    exact hNone (Or.inr (Or.inl
      ⟨G, xs, out, hSource, hMissing, hTouches⟩))
  have hLocalTests :
      ∀ {X : Type} (E : Structure L X),
        E.Irreducible →
        ∀ e : Structure.Embedding E Source,
          (∃ x : X, e x ∈ S) →
          ∃ ge : Structure.Embedding E Target,
            ∀ x : X, ge x = g (e x) := by
    intro X E hIr e hTouches
    by_contra hMissing
    exact hNone (Or.inr (Or.inr
      ⟨X, E, hIr, e, hTouches, hMissing⟩))
  exact hNoNewEHN
    ((ehn_map_changedOnSet_iff_localNativeVerification
      Source Target f g hf S hAway).2
        ⟨hLocalRelations, hLocalFunctions, hLocalTests⟩)

/-- A concrete setwise collision-repair obstruction for an ACTUAL
support-first, seam-collision-second minimal forbidden EHN witness.

Suppose a candidate g changes arbitrary ORIGINAL source vertices S
whose OLD and NEW images BOTH lie in the genuine common seam, leaves
all source vertices outside S unchanged, and STRICTLY reduces the
ordered seam-collision SOURCE-pair count. No assumption that its
new target seam points are unused is required.

If all three exact ORIGINAL local EHN checks succeeded, g would be
an EHN map of the SAME original forbidden source. This contradicts
the chosen lexicographic minimizer. Hence a real positive old
relation, native function incidence (input OR output), or irreducible
full source test MEETING S must block g.

This gives an exact diagnostic for multi-vertex source-hull
recolouring, but DOES NOT construct a successful repair, change the
source, or prove unrestricted original 2019 Claim 2. -/
theorem lexMinimalForbiddenWitness_collisionDroppingSetwiseSeamRecolor_has_localNativeFailure
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
    (S : Set w.Carrier)
    (g : w.Carrier → UT)
    (hAway : ∀ x : w.Carrier, x ∉ S → g x = w.toTarget x)
    (hChangedSeam : ∀ x : w.Carrier, x ∈ S →
      w.toTarget x ∈ Seam ∧ g x ∈ Seam)
    (hCollisionDrop :
      Nat.card {p : w.Carrier × w.Carrier //
        p.1 ≠ p.2 ∧ g p.1 = g p.2 ∧ g p.1 ∈ Seam} <
        w.seamCollisionPairCount Seam) :
    (∃ (R : L.RelSymbol)
        (xs : Fin (L.relArity R) → w.Carrier),
      w.source.rel R xs ∧
      ¬ Target.rel R (g ∘ xs) ∧
      ∃ i : Fin (L.relArity R), xs i ∈ S) ∨
    (∃ (G : L.FuncSymbol)
        (xs : Fin (L.funcArity G) → w.Carrier)
        (out : w.Carrier),
      out ∈ w.source.func G xs ∧
      g out ∉ Target.func G (g ∘ xs) ∧
      (out ∈ S ∨ ∃ i : Fin (L.funcArity G), xs i ∈ S)) ∨
    (∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E w.source,
        (∃ x : X, e x ∈ S) ∧
        ¬ ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x = g (e x)) := by
  have hStay : ∀ x : w.Carrier,
      w.toTarget x ∈ Seam → g x ∈ Seam := by
    intro x hx
    by_cases hs : x ∈ S
    · exact (hChangedSeam x hs).2
    · simpa [hAway x hs] using hx
  have hFixed : ∀ x : w.Carrier,
      w.toTarget x ∉ Seam → g x = w.toTarget x := by
    intro x hx
    apply hAway
    intro hs
    exact hx (hChangedSeam x hs).1
  have hNotEHN :
      ¬ w.source.IsEHNHomomorphismEmbedding Target g := by
    intro hg
    exact lexMinimalForbiddenWitness_no_seamOnlyCollisionReducingEHNRecoloring
      LeftExclusive Seam hDisjoint w hPrimary hSecondary
      g hg hStay hFixed hCollisionDrop
  exact ehn_map_changedOnSet_failure_has_localNativeWitness
    w.source Target w.toTarget g w.homEmbedding
    S hAway hNotEHN

end AllThoseRamseyClasses.Lifts
