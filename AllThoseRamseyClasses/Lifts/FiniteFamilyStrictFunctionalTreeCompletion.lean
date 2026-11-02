import AllThoseRamseyClasses.Lifts.FunctionalCopywiseFreeFold
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceStrongAmalgamation
import PartiteConstruction.Functional.RankedTreeReduct

/-!
# Track E: finite strong-AP copywise completion of STRICT functional B-trees

The maximal induced-trace age of a finite named forbidden family is
hereditary and has genuine finite full-functional STRONG amalgamation,
but its amalgam can add mixed component-tag relations. We use exactly
that strong amalgamation, never an unsupported free-amalgamation
assertion about the expanded age.

A STRICT native functional tree of full copies of a fixed irreducible
expanded B is constructed by finite full-function free amalgamations
of earlier trees, whose gluing roots lie in full irreducible
substructures of the source sides. Every such irreducible source
substructure lies in a constituent full B-copy, by the verified
functional tree localization lemma.

An existing B-copywise completion of a side therefore embeds each
gluing root fully into its finite age target. Strong amalgamation
combines the two finite age targets over these FULL root embeddings.
A compatible fold across the free SOURCE diagram then preserves
every B-copy as a full expanded functional embedding in the new
age target, even though the target is not a free amalgam.

This is the functional analogue of the verified relational
TreeAmalgam.copywiseCompletion_inStrongClass, specialized to the
actual finite-family maximal-trace age. Complete old set-valued
function fibres are reflected on every protected B-copy; the
completion vertex map need not preserve any fibre globally.
No arbitrary clipped weak induced subset is treated as a full
functional substructure.

The theorem closes the STRICT functional B-tree strong-AP
completion step, not the harder sparsening theorem that must
produce such a strict tree from each exact weak local test while
maintaining the Ramsey arrow and distinguished Bbar marks.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A B-copywise completion of a strict functional B-tree gives a
FULL embedding of every strict gluing root into the completed
target. The root itself need not be a member of the age.

The only nontrivial geometric hypothesis is that the root's image
lies in a FULL irreducible piece on the source tree side.
That piece is localized inside one actual B-copy before
applying copywise completion. -/
theorem FunctionalCopywiseCompletion.on_strictRoot
    {M : Language.{u}}
    {VB VH VW VT : Type}
    {Base : Structure M VB}
    {Root : Structure M VH}
    {T : Structure M VW}
    {Target : Structure M VT}
    (hTree : Structure.TreeAmalgam Base VW T)
    (s : Structure.Embedding Root T)
    (hContainer : s.ContainedInIrreducible)
    (f : VW → VT)
    (hCopy : FunctionalCopywiseCompletion Base T Target f) :
    ∃ e : Structure.Embedding Root Target,
      ∀ x : VH, e x = f (s x) := by
  classical
  obtain ⟨VE, E, hE, j, hInside⟩ := hContainer
  obtain ⟨β, hβ⟩ :=
    hTree.irreducible_contained_in_copy hE j
  have hRange : ∀ x : VH, ∃ b : VB, s x = β b := by
    intro x
    obtain ⟨a, hxa⟩ := hInside x
    obtain ⟨b, hab⟩ := hβ a
    exact ⟨b, hxa.trans hab⟩
  let eB : Structure.Embedding Root Base :=
    s.factorThroughRange β hRange
  obtain ⟨βT, hβT⟩ := hCopy β
  refine ⟨βT.comp eB, ?_⟩
  intro x
  calc
    (βT.comp eB) x = βT (eB x) := rfl
    _ = f (β (eB x)) := hβT (eB x)
    _ = f (s x) := by
      apply congrArg f
      exact (Classical.choose_spec (hRange x)).symm

/-- Every STRICT full-functional tree of copies of an
IRREDUCIBLE finite maximal-trace age member B has a
finite B-copywise completion in the SAME maximal-trace age.

The target is an actual finite expansion with exact old
function fibres. It can have extra mixed component predicates:
we require only B-copywise FULL embeddings, not a globally
full embedding of the tree. No false expanded free AP is used.

This conclusion is the functional strong-AP tree-completion
ingredient of E2, not the full Ramsey theorem. -/
theorem finiteNamedMaximalTraceAge_strictTree_copywiseCompletion
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    {VB WT : Type}
    (B : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VB)
    (hB : IsFiniteNamedMaximalTrace Family B)
    (hIrred : B.Irreducible)
    {T : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) WT}
    (hTree : Structure.TreeAmalgam B WT T) :
    ∃ (VT : Type)
      (Target : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family Target ∧
      ∃ (f : WT → VT),
        FunctionalCopywiseCompletion B T Target f := by
  classical
  induction hTree with
  | @copy Wcopy Tcopy j hsurj =>
      let inv : Structure.Embedding Tcopy B :=
        (Structure.Embedding.id Tcopy).factorThroughRange j
          (fun t => by
            obtain ⟨b, hb⟩ := hsurj t
            exact ⟨b, hb.symm⟩)
      refine ⟨VB, B, hB, inv, ?_⟩
      intro e
      exact ⟨inv.comp e, by intro x; rfl⟩
  | @glue W₁ W₂ H W T₁ T₂ Root Whole
      h₁ h₂ sL sR hcL hcR iL iR hfree ihL ihR =>
      obtain ⟨V₁, D₁, hD₁, fL, hCopiesL⟩ := ihL
      obtain ⟨V₂, D₂, hD₂, fR, hCopiesR⟩ := ihR
      obtain ⟨rootL, hRootL⟩ :=
        FunctionalCopywiseCompletion.on_strictRoot
          h₁ sL hcL fL hCopiesL
      obtain ⟨rootR, hRootR⟩ :=
        FunctionalCopywiseCompletion.on_strictRoot
          h₂ sR hcR fR hCopiesR
      obtain ⟨VT, Target, hTarget, jL, jR, hOverlap⟩ :=
        finiteNamedMaximalTraceAge_strongAmalgamation
          Family Root D₁ D₂ hD₁ hD₂ rootL rootR
      have hCompatible :
          ∀ d : H, jL (fL (sL d)) = jR (fR (sR d)) := by
        intro d
        calc
          jL (fL (sL d)) = jL (rootL d) :=
            congrArg jL (hRootL d).symm
          _ = jR (rootR d) :=
            (hOverlap (rootL d) (rootR d)).mpr
              ⟨d, rfl, rfl⟩
          _ = jR (fR (sR d)) :=
            congrArg jR (hRootR d)
      let f : W → VT :=
        functionalCompatibleFold hfree
          (jL ∘ fL) (jR ∘ fR) hCompatible
      have hCopies :
          FunctionalCopywiseCompletion B Whole Target f :=
        FunctionalCopywiseCompletion.fold_free
          hIrred hfree fL fR hCopiesL hCopiesR
          jL jR hCompatible
      exact ⟨VT, Target, hTarget, f, hCopies⟩

end AllThoseRamseyClasses.Lifts
