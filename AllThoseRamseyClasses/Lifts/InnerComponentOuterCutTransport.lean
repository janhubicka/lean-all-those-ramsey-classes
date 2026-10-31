import AllThoseRamseyClasses.Lifts.GeneratedInnerRootOuterCutAttachment

/-!
# A geometric inner component survives a nonnested older outer cut

A genuine inner minimal-separator piece has a connected component
D outside its own whole closed root U. In a contextual B-only
source flip, the OLD outer root T belongs to the unchanged full
native complement; the newly inserted selected inner component
D' is private to the new piece and DISJOINT from T.

There is no inclusion T⊆U or U⊆T in general. Nonetheless, EVERY
Gaifman path in D' avoiding U stays in D' and, because D'∩T=∅,
is also a path avoiding T. Consequently D' belongs to ONE actual
component of the NEW source after deleting T.

The previously verified generated-boundary attachment theorem
then applies. Since U = Cl(N(D')) for any genuine minimal
closed-separator piece, ALL inner-root vertices in U\T belong
to that SAME exterior-T component. This gives two exact,
unconditional source-geometric invariants of a nested flip,
without identifying different source vertices via a weak EHN map.

The remaining work for the printed 2019 Claim 2 is to connect
the retained old interior vertices in the unchanged complement
to this component, and prove that its whole generated boundary
against the transported old outer root is still complete T.
The full rooted incompatibility profile is a further obligation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V : Type v}

/-- The entire selected component D outside a cut U stays
inside ONE component after deleting a possibly incomparable cut
T, provided D is disjoint from T. No closedness of either cut
is needed for this pure Gaifman-path transport.

This is the missing nondisjoint-cut lemma: the standard
monotonicity theorem only applies when T⊆U. -/
theorem innerComponent_subset_outerComponent_of_disjoint
    (A : Structure L V)
    (U T : Set V)
    (d : {v : V // v ∉ U})
    (hDisjoint :
      Disjoint (componentFrom A.graph U d) T) :
    ∃ x : {v : V // v ∉ T},
      x.1 = d.1 ∧
      componentFrom A.graph U d ⊆
        componentFrom A.graph T x := by
  have hdC : d.1 ∈ componentFrom A.graph U d :=
    componentFrom_root A.graph U d
  have hdNotT : d.1 ∉ T :=
    (Set.disjoint_left.mp hDisjoint) hdC
  let x : {v : V // v ∉ T} := ⟨d.1, hdNotT⟩
  have hTransport (z : {v : V // v ∉ U})
      (hz : ReachOutside A.graph U d z) :
      z.1 ∈ componentFrom A.graph T x := by
    induction hz with
    | refl =>
        exact componentFrom_root A.graph T x
    | @tail a b hab hedge ih =>
        have hbInD : b.1 ∈ componentFrom A.graph U d :=
          ⟨b.2, hab.tail hedge⟩
        have hbNotT : b.1 ∉ T :=
          (Set.disjoint_left.mp hDisjoint) hbInD
        exact componentFrom_step A.graph T x ih hbNotT hedge
  refine ⟨x, rfl, ?_⟩
  intro z hz
  exact hTransport ⟨z, hz.1⟩ hz.2

/-- For a genuine inner minimal-separator piece whose selected
component D avoids the old OUTER closed root T, there is an
actual surviving outer-T component containing (1) ALL of D and
(2) EVERY vertex of the inner root U not deleted by T.

This follows from the real generated boundary U=Cl(N(D)),
not an assumption that root vertices are direct neighbours.
It works with arbitrary arities and nullary native functions. -/
theorem minimalInnerPiece_survivesOuterCut_withWholeGeneratedRoot
    (A : Structure L V)
    (T : Set V) (hTclosed : A.IsClosed T)
    {U : Set V}
    (a b : {v : V // v ∉ U})
    (hMin : IsMinimalClosedSeparator A U a b)
    (hDisjoint :
      Disjoint (componentFrom A.graph U a) T) :
    ∃ x : {v : V // v ∉ T},
      x.1 = a.1 ∧
      componentFrom A.graph U a ⊆
        componentFrom A.graph T x ∧
      U \ T ⊆ componentFrom A.graph T x := by
  obtain ⟨x, hx, hD⟩ :=
    innerComponent_subset_outerComponent_of_disjoint
      A U T a hDisjoint
  have hRoot : U \ T ⊆ componentFrom A.graph T x :=
    minimalInnerRoot_outsideClosedOuterCut_attaches
      A T hTclosed x a b hMin hD
  exact ⟨x, hx, hD, hRoot⟩

end AllThoseRamseyClasses.Lifts
