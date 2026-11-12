import AllThoseRamseyClasses.Published.TrackEJointHybridExactInduce
import PartiteConstruction.Ramsey.ClosureEmbeddingRange
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Track E2: FULL HYBRID root tagging preserves relational free amalgams

A full-root hybrid tag contains one positive OLD tuple, whose
entire vertex tuple lies in one side of any genuine relational free
amalgam. Every FULL input-root coordinate is displayed among that
tuple's designated input positions. Hence the complete hybrid root
embedding has image contained in that same side and factors through
the side's FULL induced embedding.

We formalize the underlying root-factorization once for an arbitrary
relational symbol and any chosen displayed prefix of its tuple. This
single lemma applies to both:
* positive singleton-by-output-part function incidences, whose
  distinct input prefix uses Fin.castSucc;
* original complete multivalued output tuples, whose distinct
  input prefix uses Fin.castAdd mask.size.

Consequently a genuine free-amalgamation diagram of arbitrary
BASE hybrid relational structures remains a genuine relational
free-amalgamation diagram after the NEW joint full-hybrid-root
tag expansion, with the EXACT same vertex maps and overlap.

This is the canonical source-side free-attachment property required
for an eventual corrected 2019 hybrid partite construction.
It does NOT prove that arbitrary noncanonical hybrid targets decode
to a native System, nor strong AP of the constrained completion
class, uniform local certificates, or the ordered sparse Ramsey
witness. There is no weak-set closure hull or extra root vertex.
-/

namespace StructuralRamsey.RelStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- In a genuine relational free amalgam, an OLD tuple together
with any full embedded test root on displayed tuple coordinates
localizes to the same side. This handles arbitrary relational
symbol arity and a finite root carrier in a DIFFERENT universe. -/
private theorem fullHybridTagRoot_freeSide
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (R : (L.splitMaskHybrid Parts).Symbol)
    (n : ℕ)
    (inputPos :
      Fin n → Fin ((L.splitMaskHybrid Parts).arity R))
    (Test : RelStructure (L.splitMaskHybrid Parts) (Fin n))
    (t : Fin ((L.splitMaskHybrid Parts).arity R) → C)
    (hOld : Whole.rel R t)
    (g : Embedding Test Whole)
    (hRoot : ∀ i : Fin n, t (inputPos i) = g i) :
    (∃ (x : Fin ((L.splitMaskHybrid Parts).arity R) → E),
        Left.rel R x ∧
        (∃ e : Embedding Test Left,
          ∀ i : Fin n, x (inputPos i) = e i) ∧
        t = iL ∘ x) ∨
    (∃ (x : Fin ((L.splitMaskHybrid Parts).arity R) → F),
        Right.rel R x ∧
        (∃ e : Embedding Test Right,
          ∀ i : Fin n, x (inputPos i) = e i) ∧
        t = iR ∘ x) := by
  classical
  rcases (hFree.rel_iff R t).mp hOld with
      ⟨x, hx, htx⟩ | ⟨x, hx, htx⟩
  · have hRange : ∀ i : Fin n, ∃ a : E, g i = iL a := by
      intro i
      refine ⟨x (inputPos i), ?_⟩
      calc
        g i = t (inputPos i) := (hRoot i).symm
        _ = iL (x (inputPos i)) := congrFun htx (inputPos i)
    let e : Embedding Test Left :=
      g.factorThroughRangeHeterogeneous iL hRange
    have hFactor (i : Fin n) : g i = iL (e i) :=
      Classical.choose_spec (hRange i)
    refine Or.inl ⟨x, hx, ⟨e, ?_⟩, htx⟩
    intro i
    apply iL.injective
    calc
      iL (x (inputPos i)) = t (inputPos i) :=
        (congrFun htx (inputPos i)).symm
      _ = g i := hRoot i
      _ = iL (e i) := hFactor i
  · have hRange : ∀ i : Fin n, ∃ b : F, g i = iR b := by
      intro i
      refine ⟨x (inputPos i), ?_⟩
      calc
        g i = t (inputPos i) := (hRoot i).symm
        _ = iR (x (inputPos i)) := congrFun htx (inputPos i)
    let e : Embedding Test Right :=
      g.factorThroughRangeHeterogeneous iR hRange
    have hFactor (i : Fin n) : g i = iR (e i) :=
      Classical.choose_spec (hRange i)
    refine Or.inr ⟨x, hx, ⟨e, ?_⟩, htx⟩
    intro i
    apply iR.injective
    calc
      iR (x (inputPos i)) = t (inputPos i) :=
        (congrFun htx (inputPos i)).symm
      _ = g i := hRoot i
      _ = iR (e i) := hFactor i

namespace IsFreeAmalgam

/-- The FULL joint split/mask hybrid-root tagging functor preserves
genuine relational free-amalgamation diagrams on the EXACT same
vertices. Root factorization uses the displayed input positions,
not a closure hull, and works for BOTH fresh tag families.

No U-closedness assumption is required for this source-side fact. -/
theorem splitMaskJointRoot
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR) :
    IsFreeAmalgam
      sL.splitMaskJointRoot sR.splitMaskJointRoot
      iL.splitMaskJointRoot iR.splitMaskJointRoot := by
  classical
  refine {
    covers := hFree.covers
    overlap := hFree.overlap
    rel_iff := ?_
  }
  intro R t
  rcases R with R | R
  · exact hFree.rel_iff R t
  · rcases R with p | p
    · constructor
      · rintro ⟨hOld, g, hRoot⟩
        rcases fullHybridTagRoot_freeSide hFree
            (Language.hybridSplitOutputSymbol p.input)
            p.input.rootSize
            (fun i : Fin p.input.rootSize => i.castSucc)
            p.root t hOld g hRoot with hL | hR
        · obtain ⟨x, hx, ⟨e, he⟩, htx⟩ := hL
          exact Or.inl ⟨x, ⟨hx, e, he⟩, htx⟩
        · obtain ⟨x, hx, ⟨e, he⟩, htx⟩ := hR
          exact Or.inr ⟨x, ⟨hx, e, he⟩, htx⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact (iL.splitMaskJointRoot.map_rel_iff
            (.inr (.inl p)) x).mpr hx
        · exact (iR.splitMaskJointRoot.map_rel_iff
            (.inr (.inl p)) x).mpr hx
    · constructor
      · rintro ⟨hOld, g, hRoot⟩
        rcases fullHybridTagRoot_freeSide hFree
            (Language.hybridOriginalMaskOutputSymbol
              p.input p.mask)
            p.input.rootSize
            (fun i : Fin p.input.rootSize =>
              Fin.castAdd p.mask.size i)
            p.root t hOld g hRoot with hL | hR
        · obtain ⟨x, hx, ⟨e, he⟩, htx⟩ := hL
          exact Or.inl ⟨x, ⟨hx, e, he⟩, htx⟩
        · obtain ⟨x, hx, ⟨e, he⟩, htx⟩ := hR
          exact Or.inr ⟨x, ⟨hx, e, he⟩, htx⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact (iL.splitMaskJointRoot.map_rel_iff
            (.inr (.inr p)) x).mpr hx
        · exact (iR.splitMaskJointRoot.map_rel_iff
            (.inr (.inr p)) x).mpr hx

end IsFreeAmalgam
end StructuralRamsey.RelStructure
