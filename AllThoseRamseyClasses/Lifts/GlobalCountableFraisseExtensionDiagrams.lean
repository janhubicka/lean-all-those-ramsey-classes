import AllThoseRamseyClasses.Lifts.GlobalOriginalSection3FraisseInput
import PartiteConstruction.Structure.Basic

/-!
# Track F: countable genuine finite extension diagrams

The original regular global maximal-trace age has a countable
type of actual labelled finite representatives on carriers Fin n.
Every pair of these representatives has only FINITELY many full
functional embeddings, because both vertex carriers are finite.
Hence the type of ALL representative extension diagrams A ↪ B
is countable, with no assumption that A or B is irreducible,
one-point-generated, or of bounded size.

For any fixed genuine finite stage X of the age, a *request* is
such a diagram plus a FULL root embedding A ↪ X. The set of all
requests at that stage is also countable. For each fixed diagram,
the set of its root embeddings into X is finite.

These are the countability/bookkeeping prerequisites for scheduling
all finite requests in a Fraïssé chain. The finite realization lemma
is a different module (Track F #825). No direct limit, convergence
or infinite ultrahomogeneous structure is claimed here.

Every embedding uses the original complete functional value-set
equality. The numbered ramsey.tex is frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- An ACTUAL finite full extension diagram between two members
of the original maximal-trace representative type.
Its source and target carriers can have different finite sizes.
The root arrow is a genuine FULL structural embedding. -/
abbrev GlobalOriginalFiniteTraceDiagram
    (F : ∀ {W : Type}, Structure L W → Prop) :=
  Σ P : GlobalOriginalFiniteTraceRepresentatives F,
    Σ Q : GlobalOriginalFiniteTraceRepresentatives F,
      Structure.Embedding P.2.1 Q.2.1

/-- The finite-age Fraïssé input provides a countable type of
ALL actual representative extension diagrams. The fibres
over two representatives are finite by full embedding finiteness,
so no false uniform bound on forbidden-source size is needed. -/
theorem globalOriginalFiniteTraceDiagrams_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F) :
    Countable (GlobalOriginalFiniteTraceDiagram F) := by
  classical
  letI : Countable (GlobalOriginalFiniteTraceRepresentatives F) :=
    hInput.countableRepresentatives
  letI (P Q : GlobalOriginalFiniteTraceRepresentatives F) :
      Finite (Structure.Embedding P.2.1 Q.2.1) := inferInstance
  infer_instance

/-- A request to extend one rooted finite diagram at a fixed
finite stage X consists of the diagram A ↪ B and one actual
FULL embedding of its root A into X. The existence of this
root embedding is NOT implied by mere age membership. -/
abbrev GlobalOriginalFiniteTraceStageRequest
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX) :=
  Σ d : GlobalOriginalFiniteTraceDiagram F,
    Structure.Embedding d.1.2.1 X

/-- Every specific finite extension diagram has only finitely
many full root embeddings into a fixed finite age member X.
This includes full reflection of the added relation tables and
the complete old partial/set-valued function fibres. -/
theorem globalOriginalFiniteTrace_fixedRootEmbeddings_finite
    (F : ∀ {W : Type}, Structure L W → Prop)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X)
    (d : GlobalOriginalFiniteTraceDiagram F) :
    Finite (Structure.Embedding d.1.2.1 X) := by
  letI : Finite VX := hX.1
  infer_instance

/-- The full collection of finite extension requests at one
age stage X is COUNTABLE. This is a countable sigma over
the actual diagram type, with finite full-root-embedding fibres.
No assumption of a countably generated native closure or
an existing infinite Fraïssé limit is introduced. -/
theorem globalOriginalFiniteTraceStageRequests_countable
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VX : Type}
    (X : Structure (globalFunctionalPieceLanguage F) VX)
    (hX : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) X) :
    Countable (GlobalOriginalFiniteTraceStageRequest F X) := by
  classical
  letI : Countable (GlobalOriginalFiniteTraceDiagram F) :=
    globalOriginalFiniteTraceDiagrams_countable F hInput
  letI (d : GlobalOriginalFiniteTraceDiagram F) :
      Finite (Structure.Embedding d.1.2.1 X) :=
    globalOriginalFiniteTrace_fixedRootEmbeddings_finite F X hX d
  infer_instance

end AllThoseRamseyClasses.Lifts
