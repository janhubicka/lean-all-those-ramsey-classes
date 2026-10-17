import AllThoseRamseyClasses.Applications.TotallyOrderedIncidenceWeakTagDecoding
import Mathlib.Order.PiLex
import Mathlib.Order.Prod.Lex.Basic

/-!
# Genuine positive-tuple orders in arbitrary weak incidence Ramsey witnesses

A weak orphan-tolerant incidence structure can have distinct positive r-tuples
with the SAME singleton forward output.  Consequently the output tags alone do
not linearly order the positive relation instances.

For each symbol r, assign a positive tuple the ordered pair
  (its unique F_r-output tag, its complete ordered input tuple).
The first coordinate uses the EXTERNAL linear order on the Ramsey witness.
The second uses the ordinary lexicographic order on the finite-arity input
function (including arity zero).  This PAIR is injective even when the first
coordinate is not, so pulling back the lexicographic product order yields a
genuine LinearOrder on ALL positive tuples.

Orphan tags and output collisions are deliberately allowed.  This result is
independent of whether the auxiliary's arbitrary INTERNAL order relation is
itself an order.  It is one of the decoding ingredients for manuscript thm:TO.
-/

namespace AllThoseRamseyClasses.Applications.TotallyOrderedIncidence

open StructuralRamsey
open StructuralRamsey.Structure

universe u w

/-- Genuine positive r-tuples in the old relational reduct of a weak
functional incidence structure.  No generated-tag injectivity is required. -/
abbrev WeakPositiveTuples
    {L : RelLanguage.{u}} {W : Type w}
    (C : Structure (markedIncidencePaperLanguage L) W)
    (r : L.Symbol) :=
  {t : Fin (L.arity r) → W // C.rel (.paper (.original r)) t}

/-- Lexicographic key: (singleton forward-output tag, full input tuple).
The second coordinate distinguishes tuples whenever their output tags
collide, even for an arbitrary weak auxiliary Ramsey witness. -/
noncomputable def weakPositiveTupleKey
    {L : RelLanguage.{u}} {W : Type w} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol)
    (p : WeakPositiveTuples C r) :
    Lex (W × Lex (Fin (L.arity r) → W)) :=
  toLex (weakOutputTag hC r p.1 p.2, toLex p.1)

/-- The entire pair remains injective without assuming the weak forward
function outputs themselves are injective. -/
theorem weakPositiveTupleKey_injective
    {L : RelLanguage.{u}} {W : Type w} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol) :
    Function.Injective (weakPositiveTupleKey hC r) := by
  intro p q h
  apply Subtype.ext
  have hcoord := congrArg
    (fun z : Lex (W × Lex (Fin (L.arity r) → W)) =>
      ofLex ((ofLex z).2)) h
  exact hcoord

/-- A GENUINE total (linear) order on every positive r-tuple in an
arbitrary weak incidence-law structure, determined by the external
vertex order with lexicographic input-tuple tie-breaking.
No finite-carrier or positive-arity restriction is needed. -/
noncomputable def weakPositiveTuplesLinearOrder
    {L : RelLanguage.{u}} {W : Type w} [LinearOrder W]
    {C : Structure (markedIncidencePaperLanguage L) W}
    (hC : IncidenceFunctionLaws C) (r : L.Symbol) :
    LinearOrder (WeakPositiveTuples C r) :=
  LinearOrder.lift' (weakPositiveTupleKey hC r)
    (weakPositiveTupleKey_injective hC r)

end AllThoseRamseyClasses.Applications.TotallyOrderedIncidence
