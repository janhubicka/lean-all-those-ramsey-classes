import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceMarkedPaperEmbedding
import PartiteConstruction.Structure.Order

/-!
# Canonical incidence embeddings preserve a source-matched external order

The functional EHN Ramsey theorem adds an EXTERNAL linear-order relation,
while the original manuscript incidence lift has an INTERNAL comparison
relation on the enlarged carrier. These must not be silently conflated.
For any two canonical lifted sources whose chosen external orders agree
with their manuscript incidence comparisons, the already verified FULL
marked incidence embedding lifts to a FULL embedding of the additional
externally ordered functional language. This preserves every absent
relation and every empty/singleton function fibre.

This is the functorial source-copy direction needed by the direct Ramsey
arrow. It does not assert that arbitrary unconstrained TotalOrderData has
such a compatible external order; the well-formed order condition is an
explicit hypothesis, to be discharged at the original paper's input class.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure
open AllThoseRamseyClasses.Applications.TotallyOrderedEncoding

universe u v w

/-- Canonical full embeddings preserve the extra EHN order when the
source and target canonical incidence orders have been installed as
genuine external linear orders. -/
noncomputable def markedIncidencePaperOrderedEmbedding
    {L : RelLanguage.{u}} [LinearOrder L.Symbol]
    {U : Type v} {V : Type w}
    (A : TotalOrderData L U) (B : TotalOrderData L V)
    [LinearOrder (IncidenceCarrier A)]
    [LinearOrder (IncidenceCarrier B)]
    (hOrderA : ∀ x y : IncidenceCarrier A,
      paperIncidenceLE A x y ↔ x ≤ y)
    (hOrderB : ∀ x y : IncidenceCarrier B,
      paperIncidenceLE B x y ↔ x ≤ y)
    (f : U → V) (hf : IsExactEmbedding A B f) :
    Structure.Embedding
      (markedIncidencePaperStructure A).withLinearOrder
      (markedIncidencePaperStructure B).withLinearOrder := by
  let e := markedIncidencePaperEmbedding A B f hf
  have hLe (x y : IncidenceCarrier A) :
      e x ≤ e y ↔ x ≤ y := by
    change incidenceMap A B f hf x ≤ incidenceMap A B f hf y ↔ x ≤ y
    exact ((hOrderB _ _).symm.trans
      (paperIncidenceLE_map_iff A B f hf x y)).trans (hOrderA x y)
  refine {
    toFun := e
    injective := e.injective
    map_rel_iff := ?_
    map_func := e.map_func
  }
  intro R t
  cases R with
  | inl R =>
      exact e.map_rel_iff R t
  | inr _ =>
      change e (t (0 : Fin 2)) < e (t (1 : Fin 2)) ↔
        t (0 : Fin 2) < t (1 : Fin 2)
      rw [lt_iff_le_and_ne, lt_iff_le_and_ne]
      constructor
      · rintro ⟨hle, hne⟩
        exact ⟨(hLe (t (0 : Fin 2)) (t (1 : Fin 2))).mp hle,
          fun heq => hne (congrArg e heq)⟩
      · rintro ⟨hle, hne⟩
        exact ⟨(hLe (t (0 : Fin 2)) (t (1 : Fin 2))).mpr hle,
          fun heq => hne (e.injective heq)⟩

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
