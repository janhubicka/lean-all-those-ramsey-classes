import AllThoseRamseyClasses.Published.TrackEHybridOldDomainCoherence
import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import AllThoseRamseyClasses.Published.TrackEHybridVisibleWholeSplitAgreement
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: EXACT weak-safe hybrid coherence, separated from output-value coherence

The corrected 2019 hybrid relational picture has four fundamental
coherence requirements preserved when taking EXACT induced weak
subsets of the given ambient vertex carrier:

* one original set of complete output-part DOMAIN masks per input;
* agreement between each such mask and all per-part split domains;
* every split domain has a corresponding complete original mask;
* every vertex has exactly ONE unary part predicate (even isolated
  vertices and those appearing in no function tuples).

These four laws are also preserved by genuine FULL relational free
amalgamation of the base hybrid language, with compatible common
root/side assumptions as appropriate.

A fifth, stronger law demands SAME-VERTEX agreement between a
VISIBLE complete original multivalued output tuple and its visible
per-part singleton split function incidences. The previous checked
theorem shows this fifth law for every canonical native source and
every exact induced weak test. Its stability under ARBITRARY
relational free amalgamation is NOT established: a whole original
output tuple on one side and a conflicting split output from the
other can share the same input root unless additional U-closed
root-profile compatibility applies.

We therefore package the four free-stable input/part laws as
HybridWeakInputCoherent and the fifth law separately as
HybridExactWeakCoherent. The second inherits exact weak restriction
but is NOT exported as free-amalgam stable. This prevents an
invalid target-normalization or strong-AP shortcut in the eventual
two-pass 2019 construction.

No arbitrary joint-tagged sparse target is decoded here, nor is
the finite-family ordered E2 Ramsey theorem claimed.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- Every vertex of a base hybrid relational source has EXACTLY one
unary part predicate, including isolated vertices. This is not
implied merely by output-part transversality of function incidences. -/
def HybridUniqueVertexPart
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ x : V, ∃! q : Parts,
    E.rel (.inr (.inr q)) (fun _ : Fin 1 => x)

/-- An actual native partite source has its literal unique vertex
part represented by exactly one hybrid unary predicate. -/
theorem canonicalHybrid_uniqueVertexPart
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridUniqueVertexPart A.splitMaskHybrid := by
  intro x
  refine ⟨A.part x, rfl, ?_⟩
  intro q hq
  exact hq.symm

/-- Unary part uniqueness is inherited by every literal exact
induced weak vertex subset; no generated closure is involved. -/
theorem HybridUniqueVertexPart.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridUniqueVertexPart E)
    (S : Set V) :
    HybridUniqueVertexPart (E.induce S) := by
  intro x
  obtain ⟨q, hq, hUnique⟩ := h x.1
  refine ⟨q, ?_, ?_⟩
  · exact hq
  · intro r hr
    exact hUnique r hr

/-- Unique unary vertex parts are stable under true relational
free amalgamation, with no additional root-closure assumptions.
Every vertex lies on one side and its unique part reflects
through that side's FULL hybrid relational embedding. -/
theorem HybridUniqueVertexPart.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridUniqueVertexPart Left)
    (hRight : HybridUniqueVertexPart Right) :
    HybridUniqueVertexPart Whole := by
  intro x
  rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨q, hq, hUnique⟩ := hLeft a
    have hIff (r : Parts) :
        Whole.rel (.inr (.inr r)) (fun _ : Fin 1 => x) ↔
          Left.rel (.inr (.inr r)) (fun _ : Fin 1 => a) := by
      have hEq :
          (fun _ : Fin 1 => x) = iL ∘ (fun _ : Fin 1 => a) := by
        funext k
        exact ha
      rw [hEq]
      exact iL.map_rel_iff (.inr (.inr r)) (fun _ : Fin 1 => a)
    refine ⟨q, (hIff q).mpr hq, ?_⟩
    intro r hr
    exact hUnique r ((hIff r).mp hr)
  · obtain ⟨q, hq, hUnique⟩ := hRight b
    have hIff (r : Parts) :
        Whole.rel (.inr (.inr r)) (fun _ : Fin 1 => x) ↔
          Right.rel (.inr (.inr r)) (fun _ : Fin 1 => b) := by
      have hEq :
          (fun _ : Fin 1 => x) = iR ∘ (fun _ : Fin 1 => b) := by
        funext k
        exact hb
      rw [hEq]
      exact iR.map_rel_iff (.inr (.inr r)) (fun _ : Fin 1 => b)
    refine ⟨q, (hIff q).mpr hq, ?_⟩
    intro r hr
    exact hUnique r ((hIff r).mp hr)

/-- Four INPUT/DOMAIN/PART invariants of an arbitrary base hybrid
relational structure which survive both exact weak induction
and true FULL free amalgamation of compatible diagrams.

This deliberately omits the separate CROSS-output vertex
agreement law, which is not yet known free-stable in an
arbitrary noncanonical hybrid relational class. -/
def HybridWeakInputCoherent
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  SplitMaskHybridOriginalDomainCoherent E ∧
  HybridMaskSplitDomainCompatible E ∧
  HybridSplitDomainMaskCovered E ∧
  HybridUniqueVertexPart E

/-- Every finite genuine native partite System has all four
weak-safe input/domain/part invariants on exactly its vertices. -/
theorem canonicalHybrid_weakInputCoherent
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridWeakInputCoherent A.splitMaskHybrid :=
  ⟨canonicalSplitMaskHybrid_originalDomainCoherent A,
   canonicalHybrid_maskSplitDomainCompatible A,
   canonicalHybrid_splitDomainMaskCovered A,
   canonicalHybrid_uniqueVertexPart A⟩

/-- The entire weak-safe input/domain/part package is inherited
by any literal weak vertex test S of the same ambient hybrid
structure, retaining all originally active complete OLD masks. -/
theorem HybridWeakInputCoherent.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridWeakInputCoherent E) (S : Set V) :
    HybridWeakInputCoherent (E.induce S) :=
  ⟨h.1.induce S,
   h.2.1.induce S,
   h.2.2.1.induce S,
   h.2.2.2.induce S⟩

/-- True FULL relational free amalgamation preserves all FOUR
weak-safe base-hybrid invariants. Root coherence is necessary
for the mixed original-mask domain uniqueness law, while each
of the other three laws transfers directly from the side which
contains the relevant tuple/vertex. -/
theorem HybridWeakInputCoherent.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hRoot : HybridWeakInputCoherent Root)
    (hLeft : HybridWeakInputCoherent Left)
    (hRight : HybridWeakInputCoherent Right) :
    HybridWeakInputCoherent Whole :=
  ⟨hFree.splitMaskHybridOriginalDomainCoherent
      hRoot.1 hLeft.1 hRight.1,
    hFree.hybridMaskSplitDomainCompatible
      hLeft.2.1 hRight.2.1,
    hFree.hybridSplitDomainMaskCovered
      hLeft.2.2.1 hRight.2.2.1,
    HybridUniqueVertexPart.freeAmalgam hFree
      hLeft.2.2.2 hRight.2.2.2⟩

/-- The STRONGER exact-weak-safe class additionally asks for
actual value-vertex agreement on any already visible complete
OLD output tuple and split incidence. This is not silently
declared free-amalgamation stable: cross-side conflicting value
tuples remain a genuine compatibility obligation. -/
def HybridExactWeakCoherent
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  HybridWeakInputCoherent E ∧ HybridVisibleWholeSplitAgreement E

/-- An actual finite canonical native partite presentation satisfies
the weak-safe package AND visible value-level cross-coherence. -/
theorem canonicalHybrid_exactWeakCoherent
    {V : Type w} [Finite V]
    (A : FunctionalPartite.System L Parts V) :
    HybridExactWeakCoherent A.splitMaskHybrid :=
  ⟨canonicalHybrid_weakInputCoherent A,
   canonicalHybrid_visibleWholeSplitAgreement A⟩

/-- The stronger package is also stable under EVERY literal exact
induced weak vertex restriction. It is intentionally NOT exported
as stable under arbitrary free amalgamation. -/
theorem HybridExactWeakCoherent.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridExactWeakCoherent E)
    (S : Set V) :
    HybridExactWeakCoherent (E.induce S) :=
  ⟨h.1.induce S, h.2.induce S⟩

end StructuralRamsey.RelStructure
