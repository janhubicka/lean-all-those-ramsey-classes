import AllThoseRamseyClasses.Lifts.GlobalRightToLeftPieceFlip
import AllThoseRamseyClasses.Lifts.GlobalFlipClosedOuterContext
import AllThoseRamseyClasses.Lifts.CommonLiftFlipStrictSupport

/-!
# Track C: A-exclusive anchor survives every genuine B-to-A inner source flip

The abstract well-founded local B-support descent requires that
an arbitrary intermediate contextual state remains MIXED whenever
it still has positive B-exclusive source support. A key concern:
the forbidden witness no longer minimizes A-exclusive support
after the first B-to-A replacement.

A stronger source-level invariant is available without minimality:

  If a contextual K contains an A-exclusive source vertex, and
  the whole OLD selected inner side is A-exclusive-free, then
  that witness must live on the full retained complement E.
  The literal native inner replacement keeps EVERY vertex
  of E with its exact old target value; hence the SAME A-only
  support witness survives in the transported context K'.

This is a SOURCE vertex statement, not target-image counting.
No global weak-map injectivity, selected outer minimal-cut
piece, root quotient or forbidden-family isomorphism closure.

The first lemma is completely general for two transported sets
iOldL(OldInner) ∪ iOldE(SR) and
iNewL(NewInner) ∪ iNewE(SR).
The second applies it to an ACTUAL original-2019 geometric
B-only inner piece, whose old full inner side consists only
of common-root vertices and non-A-exclusive component
vertices. This is true for every intermediate forbidden
source, not just the original A-support-minimizer.

The outer contextual set K need only CONTAIN that entire
inner piece; its native closure/no-escape and full profile
are handled by the independent Track C theorems.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Any actual A-only source vertex inside an old contextual
free-amalgam carrier survives replacement of the COMPLETE
left side when that old left side has NO A-only source vertex,
and the right complement retains its exact target coordinates.

This elementary lemma needs no outer geometric structure,
closedness, finiteness, or even a free-amalgam assumption.
The two context carriers are genuine subsets of the old/new
source types, not quotients of weak target images. -/
theorem fullReplacement_context_retains_positiveSourceSupport
    {OL NL E V W T : Type}
    {OldLeft : Structure L OL}
    {NewLeft : Structure L NL}
    {Complement : Structure L E}
    {Old : Structure L V} {New : Structure L W}
    (iOldL : Structure.Embedding OldLeft Old)
    (iOldE : Structure.Embedding Complement Old)
    (iNewL : Structure.Embedding NewLeft New)
    (iNewE : Structure.Embedding Complement New)
    (SR : Set E)
    (f : V → T) (g : W → T) (AOnly : Set T)
    (hNoOldLeft : ∀ a : OL, f (iOldL a) ∉ AOnly)
    (hSameComplement : ∀ b : E,
      g (iNewE b) = f (iOldE b))
    (hOldAnchor :
      ∃ v : V,
        v ∈ (iOldL '' (Set.univ : Set OL) ∪
          iOldE '' SR) ∧ f v ∈ AOnly) :
    ∃ w : W,
      w ∈ (iNewL '' (Set.univ : Set NL) ∪
        iNewE '' SR) ∧ g w ∈ AOnly := by
  obtain ⟨v, hvK, hvA⟩ := hOldAnchor
  rcases hvK with hvLeft | hvRight
  · obtain ⟨a, _ha, haVal⟩ := hvLeft
    exfalso
    exact hNoOldLeft a (by rw [haVal]; exact hvA)
  · obtain ⟨b, hbSR, hbVal⟩ := hvRight
    refine ⟨iNewE b, Or.inr ⟨b, hbSR, rfl⟩, ?_⟩
    rw [hSameComplement b, hbVal]
    exact hvA

/-- The complete OLD geometric B-only inner piece, including its
entire original closed root, contains no A-exclusive source
vertex. This is true even if the weak EHN map collides on the
remaining source vertices.

The inner root is in the shared target-root preimage, while
its selected nonroot component has no A-exclusive vertex. -/
theorem geometricBOnlyInnerPiece_noAExclusiveSource
    {V UX UA UB UT : Type}
    (Source : Structure L V)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (Target : Structure L UT) (f : V → UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f) :
    ∀ a : (geometricGlobalFunctionalChart Source d).ext.Carrier,
      f ((functionalComponentEmbedding Source
        (Set.range d.roots) d.minimal.1 d.left) a) ∉
        fullFreeLeftExclusiveTarget iLeft jLeft := by
  intro a hA
  have haLeft : a.1 ∈
      weakFreeLeftPart (sL := iLeft) (iL := jLeft) f :=
    (weakFreeLeftPart_iff_targetExclusive
      iLeft jLeft f a.1).mpr hA
  rcases a.2 with haRoot | haComponent
  · exact haLeft.2 (hRoots haRoot)
  · exact hNoLeft a.1 haComponent haLeft

/-- An ACTUAL original-global B-to-A inner replacement preserves
at least one A-exclusive SOURCE vertex in an arbitrary outer
context containing the whole old inner geometric piece.

The proof obtains a complement-side representative by the
TRUE full source free-amalgam cover, then reuses the exact
original/new complement map agreement. Neither K nor the
new context is required to be geometric minimal-cut data.

This gives a persistent A-only anchor for the proposed
well-founded B-descent on closed/no-escape contexts. -/
theorem geometricBOnlyFlip_context_retains_AExclusiveAnchor
    {V W UX UA UB UT : Type}
    (Source : Structure L V)
    {m : ℕ} (d : GeometricFunctionalPieceData Source m)
    (K : Set V)
    (hInnerInside : geometricPieceVertices Source d ⊆ K)
    (Target : Structure L UT) (f : V → UT)
    (Left : Structure L UA) (Right : Structure L UB)
    (jLeft : Structure.Embedding Left Target)
    (jRight : Structure.Embedding Right Target)
    (X : Structure L UX)
    (iLeft : Structure.Embedding X Left)
    (iRight : Structure.Embedding X Right)
    (hRoots : Set.range d.roots ⊆
      weakFreeRootPart (sL := iLeft) (iL := jLeft) f)
    (hNoLeft : ∀ z : V,
      z ∈ functionalComponentFrom Source
        (Set.range d.roots) d.left →
      z ∉ weakFreeLeftPart (sL := iLeft) (iL := jLeft) f)
    (Q : FunctionalRootExtension
      (geometricGlobalFunctionalChart Source d).root)
    (New : Structure L W)
    (iQ : Structure.Embedding Q.str New)
    (iE : Structure.Embedding
      (geometricGlobalComplementChart Source d).str New)
    (g : W → UT)
    (hSameComplement :
      ∀ b : (geometricGlobalComplementChart Source d).Carrier,
        g (iE b) = f b.1)
    (hOldAnchor : ∃ v : V, v ∈ K ∧
      f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft) :
    ∃ w : W,
      w ∈ (iQ '' (Set.univ : Set Q.Carrier) ∪
        iE '' ((functionalComponentComplementEmbedding Source
          (Set.range d.roots) d.minimal.1 d.left) ⁻¹' K)) ∧
      g w ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
  let Inner := (geometricGlobalFunctionalChart Source d).ext
  let E := geometricGlobalComplementChart Source d
  let iOldL : Structure.Embedding Inner.str Source :=
    functionalComponentEmbedding Source
      (Set.range d.roots) d.minimal.1 d.left
  let iOldE : Structure.Embedding E.str Source :=
    functionalComponentComplementEmbedding Source
      (Set.range d.roots) d.minimal.1 d.left
  let SR : Set E.Carrier := iOldE ⁻¹' K
  have hOldFree :
      Structure.IsFreeAmalgam Inner.rootEmbedding
        E.rootEmbedding iOldL iOldE :=
    geometricGlobalSource_freeDiagram Source d
  have hNoOldLeft : ∀ a : Inner.Carrier,
      f (iOldL a) ∉ fullFreeLeftExclusiveTarget iLeft jLeft :=
    geometricBOnlyInnerPiece_noAExclusiveSource
      Source d Target f Left Right jLeft jRight
      X iLeft iRight hRoots hNoLeft
  have hOldK :
      ∃ v : V,
        v ∈ (iOldL '' (Set.univ : Set Inner.Carrier) ∪
          iOldE '' SR) ∧
        f v ∈ fullFreeLeftExclusiveTarget iLeft jLeft := by
    obtain ⟨v, hvK, hvA⟩ := hOldAnchor
    refine ⟨v, ?_, hvA⟩
    rcases hOldFree.covers v with ⟨a, haEq⟩ | ⟨b, hbEq⟩
    · exact Or.inl ⟨a, Set.mem_univ _, haEq.symm⟩
    · exact Or.inr ⟨b,
        (by change iOldE b ∈ K; rw [hbEq]; exact hvK),
        hbEq.symm⟩
  exact fullReplacement_context_retains_positiveSourceSupport
    iOldL iOldE iQ iE SR f g
    (fullFreeLeftExclusiveTarget iLeft jLeft)
    hNoOldLeft hSameComplement hOldK

end AllThoseRamseyClasses.Lifts
