import AllThoseRamseyClasses.Lifts.GlobalFlipContextInducedFreeDiagram

/-!
# A named full functional diagram for a transported nested context

In a genuine full native free amalgam Whole = Left +_Root Right, retain
ALL of Left and precisely a closed right-hand subset SR containing the
whole common root.  The previous induced-context lemma proved a full
diagram on four *anonymous inverse-image subtype carriers*.  Here we
identify those sides with their mathematically intended structures:

  Whole|K = Left +_Root (Right|SR),
  K = iLeft(Left) union iRight(SR).

The result explicitly constructs the three FULL native embeddings into
the induced context, preserves their vertex coordinates on the nose, and
certifies all original relations and complete set-valued function fibres,
including nullary functions.  It uses no weak forbidden-source quotient.

This is the structural Track B bridge needed before attaching arbitrary
outer incompatibility tests to a literal contextual inner replacement.
It does NOT by itself prove that the context is a geometric minimal-cut
piece, nor that two transported outer pieces have identical all-test
incompatibility profiles.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- A root-containing, function-closed right-side restriction of a FULL
native functional amalgam admits a new full native amalgam diagram
with the actual Left carrier, the actual induced Right|SR carrier,
and the original Root.  In particular this does NOT merely give an
anonymous existential diagram on inverse-image subtype carriers. -/
theorem fullFreeAmalgam_nestedContext_namedFullDiagram
    {H A B W : Type v}
    {Root : Structure L H}
    {Left : Structure L A}
    {Right : Structure L B}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hFree : Structure.IsFreeAmalgam sL sR iL iR)
    (SR : Set B)
    (hSRClosed : Right.IsClosed SR)
    (hRootR : ∀ r : H, sR r ∈ SR) :
    let K : Set W := iL '' (Set.univ : Set A) ∪ iR '' SR
    ∃ (hK : Whole.IsClosed K)
      (sRsmall : Structure.Embedding Root (Right.induce SR hSRClosed))
      (jL : Structure.Embedding Left (Whole.induce K hK))
      (jR : Structure.Embedding (Right.induce SR hSRClosed)
        (Whole.induce K hK)),
      Structure.IsFreeAmalgam sL sRsmall jL jR ∧
      (∀ a : A, (jL a).1 = iL a) ∧
      (∀ b : SR, (jR b).1 = iR b.1) ∧
      (∀ r : H, (sRsmall r).1 = sR r) := by
  classical
  dsimp only
  let K : Set W := iL '' (Set.univ : Set A) ∪ iR '' SR
  have hUniv : Left.IsClosed (Set.univ : Set A) := by
    intro F args hargs z hz
    exact Set.mem_univ _
  have hK : Whole.IsClosed K :=
    fullFreeAmalgam_closed_union_of_closed_sides hFree
      (Set.univ : Set A) SR hUniv hSRClosed
      (fun _ => Set.mem_univ _) hRootR
  let CK : Structure L K := Whole.induce K hK
  let RS : Structure L SR := Right.induce SR hSRClosed
  let incK : Structure.Embedding CK Whole :=
    Structure.inclusion Whole K hK
  let incR : Structure.Embedding RS Right :=
    Structure.inclusion Right SR hSRClosed
  have hsRrange : ∀ r : H, ∃ b : SR, sR r = incR b := by
    intro r
    exact ⟨⟨sR r, hRootR r⟩, rfl⟩
  have hjLrange : ∀ a : A, ∃ z : K, iL a = incK z := by
    intro a
    exact ⟨⟨iL a, Or.inl ⟨a, Set.mem_univ _, rfl⟩⟩, rfl⟩
  have hjRrange :
      ∀ b : SR, ∃ z : K, (iR.comp incR) b = incK z := by
    intro b
    exact ⟨⟨iR b.1, Or.inr ⟨b.1, b.2, rfl⟩⟩, rfl⟩
  let sRsmall : Structure.Embedding Root RS :=
    sR.factorThroughClosedRange incR hsRrange
  let jL : Structure.Embedding Left CK :=
    iL.factorThroughClosedRange incK hjLrange
  let jR : Structure.Embedding RS CK :=
    (iR.comp incR).factorThroughClosedRange incK hjRrange
  have hsRval (r : H) : (sRsmall r).1 = sR r :=
    Structure.Embedding.factorThroughClosedRange_spec
      sR incR hsRrange r
  have hjLval (a : A) : (jL a).1 = iL a :=
    Structure.Embedding.factorThroughClosedRange_spec
      iL incK hjLrange a
  have hjRval (b : SR) : (jR b).1 = iR b.1 :=
    Structure.Embedding.factorThroughClosedRange_spec
      (iR.comp incR) incK hjRrange b
  have hRightPreimage : iR ⁻¹' K = SR :=
    (fullFreeAmalgam_nestedContext_exactSidePreimages
      hFree SR hRootR).2.1
  have hRightMem (b : B) (hb : iR b ∈ K) : b ∈ SR := by
    have hb' : b ∈ iR ⁻¹' K := hb
    rw [hRightPreimage] at hb'
    exact hb'
  have hContextFree :
      Structure.IsFreeAmalgam sL sRsmall jL jR := by
    refine {
      covers := ?_
      overlap := ?_
      rel_iff := ?_
      func_iff := ?_
    }
    · intro z
      rcases z.2 with ⟨a, _, ha⟩ | ⟨b, hb, hz⟩
      · exact Or.inl ⟨a, Subtype.ext (ha.symm.trans (hjLval a).symm)⟩
      · let b' : SR := ⟨b, hb⟩
        exact Or.inr ⟨b', Subtype.ext
          (hz.symm.trans (hjRval b').symm)⟩
    · intro a b
      constructor
      · intro hab
        have hval : iL a = iR b.1 := by
          calc
            iL a = (jL a).1 := (hjLval a).symm
            _ = (jR b).1 := congrArg Subtype.val hab
            _ = iR b.1 := hjRval b
        obtain ⟨r, hrL, hrR⟩ :=
          (hFree.overlap a b.1).mp hval
        refine ⟨r, hrL, ?_⟩
        apply Subtype.ext
        exact hrR.trans (hsRval r).symm
      · rintro ⟨r, rfl, rfl⟩
        apply Subtype.ext
        calc
          (jL (sL r)).1 = iL (sL r) := hjLval (sL r)
          _ = iR (sR r) :=
            (hFree.overlap (sL r) (sR r)).mpr
              ⟨r, rfl, rfl⟩
          _ = iR (sRsmall r).1 := congrArg iR (hsRval r).symm
          _ = (jR (sRsmall r)).1 := (hjRval (sRsmall r)).symm
    · intro Rel xs
      constructor
      · intro hxs
        have hw : Whole.rel Rel (incK ∘ xs) :=
          (incK.map_rel_iff Rel xs).mpr hxs
        rcases (hFree.rel_iff Rel (incK ∘ xs)).mp hw with
          ⟨as, has, heq⟩ | ⟨bs, hbs, heq⟩
        · refine Or.inl ⟨as, has, ?_⟩
          funext k
          apply Subtype.ext
          exact (congrFun heq k).trans (hjLval (as k)).symm
        · have hbSR (k : Fin (L.relArity Rel)) : bs k ∈ SR := by
            apply hRightMem
            have hk : (xs k).1 = iR (bs k) := congrFun heq k
            rw [← hk]
            exact (xs k).2
          let bs' : Fin (L.relArity Rel) → SR :=
            fun k => ⟨bs k, hbSR k⟩
          have hbs' : RS.rel Rel bs' := hbs
          refine Or.inr ⟨bs', hbs', ?_⟩
          funext k
          apply Subtype.ext
          exact (congrFun heq k).trans (hjRval (bs' k)).symm
      · rintro (⟨as, has, rfl⟩ | ⟨bs, hbs, rfl⟩)
        · exact (jL.map_rel_iff Rel as).mpr has
        · exact (jR.map_rel_iff Rel bs).mpr hbs
    · intro Fn xs y
      constructor
      · intro hy
        have hw : incK y ∈ Whole.func Fn (incK ∘ xs) := by
          have hmem : incK y ∈
              imageSet incK (CK.func Fn xs) := ⟨y, hy, rfl⟩
          rw [incK.map_func Fn xs] at hmem
          exact hmem
        rcases (hFree.func_iff Fn (incK ∘ xs) (incK y)).mp hw with
          ⟨as, a, ha, hargs, hout⟩ |
          ⟨bs, b, hb, hargs, hout⟩
        · refine Or.inl ⟨as, a, ha, ?_, ?_⟩
          · funext k
            apply Subtype.ext
            exact (congrFun hargs k).trans
              (hjLval (as k)).symm
          · apply Subtype.ext
            exact hout.trans (hjLval a).symm
        · have haSR (k : Fin (L.funcArity Fn)) : bs k ∈ SR := by
            apply hRightMem
            have hk : (xs k).1 = iR (bs k) := congrFun hargs k
            rw [← hk]
            exact (xs k).2
          have hbSR : b ∈ SR := by
            apply hRightMem
            have hk : y.1 = iR b := hout
            rw [← hk]
            exact y.2
          let as' : Fin (L.funcArity Fn) → SR :=
            fun k => ⟨bs k, haSR k⟩
          let b' : SR := ⟨b, hbSR⟩
          have hb' : b' ∈ RS.func Fn as' := hb
          refine Or.inr ⟨as', b', hb', ?_, ?_⟩
          · funext k
            apply Subtype.ext
            exact (congrFun hargs k).trans
              (hjRval (as' k)).symm
          · apply Subtype.ext
            exact hout.trans (hjRval b').symm
      · rintro (⟨as, a, ha, rfl, rfl⟩ |
          ⟨bs, b, hb, rfl, rfl⟩)
        · have hmem : jL a ∈ imageSet jL (Left.func Fn as) :=
            ⟨a, ha, rfl⟩
          rw [jL.map_func Fn as] at hmem
          exact hmem
        · have hmem : jR b ∈ imageSet jR (RS.func Fn bs) :=
            ⟨b, hb, rfl⟩
          rw [jR.map_func Fn bs] at hmem
          exact hmem
  exact ⟨hK, sRsmall, jL, jR, hContextFree,
    hjLval, hjRval, hsRval⟩


/-- Apply the named native diagram to the ACTUAL transported geometric
outer context in Section 3 Claim 2.  The replacement source may have
different vertices inside Q; the retained part is exactly the old
full functional complement restricted to the old outer piece.

This builds a full source diagram on the true contextual carrier,
without assuming a transported geometric minimal separator or
any profile-equivalence conclusion. -/
theorem geometricOuterContext_has_namedFullDiagram
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
      (geometricGlobalComplementChart Old d).rootEmbedding iQ iE) :
    let E := geometricGlobalComplementChart Old d
    let SR := oldOuterContextInInnerComplement Old P d
    let hSR : E.str.IsClosed SR :=
      oldOuterContextInInnerComplement_isClosed Old P d
    let K : Set W :=
      iQ '' (Set.univ : Set Q.Carrier) ∪ iE '' SR
    ∃ (hK : New.IsClosed K)
      (sE : Structure.Embedding
        (geometricGlobalFunctionalChart Old d).root
        (E.str.induce SR hSR))
      (jQ : Structure.Embedding Q.str (New.induce K hK))
      (jE : Structure.Embedding (E.str.induce SR hSR)
        (New.induce K hK)),
      Structure.IsFreeAmalgam Q.rootEmbedding sE jQ jE ∧
      (∀ q : Q.Carrier, (jQ q).1 = iQ q) ∧
      (∀ e : SR, (jE e).1 = iE e.1) ∧
      (∀ r : Fin m, (sE r).1 = E.rootEmbedding r) := by
  exact fullFreeAmalgam_nestedContext_namedFullDiagram
    hFree (oldOuterContextInInnerComplement Old P d)
    (oldOuterContextInInnerComplement_isClosed Old P d)
    (oldOuterContext_contains_innerRoot Old P d hInnerRoot)

end AllThoseRamseyClasses.Lifts
