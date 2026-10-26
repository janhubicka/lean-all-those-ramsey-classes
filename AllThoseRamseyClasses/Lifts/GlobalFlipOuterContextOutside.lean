import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext

/-!
# Exact vertex support OUTSIDE a native inner-piece replacement context

For a genuine full functional amalgam New = Q +_U E, form a context
from ALL of Q and an arbitrary E-side vertex subset SE containing
the entire shared root U. The complement of that context in New
consists EXACTLY of the vertices from E \ SE. This is an actual
bijection of source vertices, not an equality of weak images.

For Section 3 Claim 2, take E to be the unchanged complement of
the flipped B-only piece, and SE the inverse image of an old
geometric outer piece P. The theorem therefore identifies ALL new
vertices outside the transported outer context as precisely the
unchanged-complement vertices formerly lying outside P.

This is necessary to compare local B-support before and after
a contextual flip. It does NOT yet assert that the transported
context is an inclusion-minimal rooted geometric piece or
preserves the original Myhill–Nerode incompatibility class.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- In an ACTUAL native functional free amalgam, the complement
of a context containing the WHOLE left side and a right subset
containing all shared-root vertices comes exclusively from the
unchanged right side OUTSIDE that subset.

The converse uses exact full-amalgam overlap: a right vertex
outside the selected subset cannot also be a left vertex, since
then it would be one of the included common-root images. -/
theorem fullFreeAmalgam_fullLeft_contextOutside_iff
    {H A B W : Type v}
    {Root : Structure L H}
    {Left : Structure L A} {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set B)
    (hRootR : ∀ r : H, sR r ∈ SR)
    (w : W) :
    w ∉ (iL '' (Set.univ : Set A) ∪ iR '' SR) ↔
      ∃ b : B, b ∉ SR ∧ iR b = w := by
  constructor
  · intro hw
    rcases hFree.covers w with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact False.elim (hw (Or.inl ⟨a, Set.mem_univ _, ha⟩))
    · refine ⟨b, ?_, hb⟩
      intro hbSR
      exact hw (Or.inr ⟨b, hbSR, hb⟩)
  · rintro ⟨b, hbNotSR, rfl⟩ hmem
    rcases hmem with hLeft | hRight
    · obtain ⟨a, _ha, hab⟩ := hLeft
      obtain ⟨r, _hra, hrb⟩ := (hFree.overlap a b).mp hab
      exact hbNotSR (by
        rw [hrb]
        exact hRootR r)
    · obtain ⟨b', hb'SR, hbb'⟩ := hRight
      have hbeq : b' = b := iR.injective hbb'
      exact hbNotSR (by simpa [hbeq] using hb'SR)

/-- In a genuine full source replacement of one nested inner piece,
ALL vertices outside the function-closed transported outer context
come from the unchanged full native inner complement, and exactly
from those complement vertices NOT belonging to the old outer piece.

The two images need not be coordinatewise distinct under an
additional weak forbidden EHN map: this uses only full embeddings
between SOURCE structures. -/
theorem geometricOuterContext_outside_iff_oldComplementOutside
    {V W : Type}
    (Old : Structure L V)
    {n m : ℕ}
    (P : GeometricFunctionalPieceData Old n)
    (d : GeometricFunctionalPieceData Old m)
    (hInnerRoot : ∀ i : Fin m,
      d.roots i ∈ geometricPieceVertices Old P)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Old d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Old d).str New)
    (hFree : Structure.IsFreeAmalgam
      Q.rootEmbedding
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE)
    (w : W) :
    w ∉ (iQ '' (Set.univ : Set Q.Carrier) ∪
      iE '' (oldOuterContextInInnerComplement Old P d)) ↔
      ∃ b : (geometricGlobalComplementChart Old d).Carrier,
        b ∉ oldOuterContextInInnerComplement Old P d ∧ iE b = w := by
  exact fullFreeAmalgam_fullLeft_contextOutside_iff
    hFree
    (oldOuterContextInInnerComplement Old P d)
    (oldOuterContext_contains_innerRoot Old P d hInnerRoot)
    w

end AllThoseRamseyClasses.Lifts
