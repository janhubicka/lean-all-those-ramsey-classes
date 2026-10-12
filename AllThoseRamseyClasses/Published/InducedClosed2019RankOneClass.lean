import AllThoseRamseyClasses.Published.InducedClosed2019UnrestrictedInitial

/-!
# A full corrected 2019 Ramsey-class theorem under rank-one local cutoffs

The unrestricted initial Picture over NON-U-CLOSED Ramsey controls
now has a constructive formalization, using correctly root-tagged
relation symbols in the recursively inserted little Picture.

Even though the GENERAL higher-rank j->j+1 Picture step remains
open, this supplies a COMPLETE positive 2019-style class theorem
when every local-completion instance has a cutoff n<=1.

The additional hypothesis below is explicit: for each B in K and
irreducible Ramsey control C0 in R, some local cutoff n<=1 works
with EXACT weak n-vertex induced tests, using the coordinated
corrected Definition 2.15/2.17 map and membership predicates.

The proof:
 * takes the ordinary finite Ramsey control C0 supplied by R,
   without requiring C0 to be U-closed;
 * obtains its cutoff n<=1 from the extra class hypothesis;
 * constructs the tagged/repaired U-closed Picture above C0;
 * finishes using rank-one protected irreducible coverage and the
   original exact weak-test local completion axiom.

This is a GENUINE finite K-Ramsey conclusion under an explicit
stronger rank-one local-finiteness condition. It is not a proof
of unrestricted repaired Theorem 2.18.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- All original corrected 2019 local-finiteness instances may
be witnessed with n<=1. The underlying locally finite
multiamalgamation hypothesis is kept separate in the theorem. -/
def Has2019LocalCutoffsAtMostOne
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L) : Prop :=
  ∀ {Y Z : Type v} [Finite Y] [Finite Z]
    (B : RelStructure L Y) (C0 : RelStructure L Z),
    K B → R C0 →
    ∃ n : ℕ, n ≤ 1 ∧
      InducedClosedULocalCompletionAt K rules B C0 n

/-- Full Ramsey property of K under the coordinated correction and
uniformly rank-one local cutoffs, with NO extra restriction on the
relative U-closedness of A copies or the initial Ramsey control.

The native recursively tagged initial Picture is built; the
higher-rank iteration is not used or postulated. -/
theorem coordinated2019_ramsey_of_cutoffs_at_most_one
    (R K : StructureClass.{u,v} (L := L))
    (rules : ClosureDescription L)
    (hR : FiniteRamseyClass R)
    (hRIrred : ∀ {X : Type v} (C : RelStructure L X),
      R C → C.Irreducible)
    (hK : IsCoordinated2019MultiamalgamationClass R K rules)
    (hCutoff : Has2019LocalCutoffsAtMostOne R K rules) :
    FiniteRamseyClass K := by
  intro X Y hFX hFY A B hKA hKB κ hFκ hNκ
  have hRA : R A := hK.induced.subset A hKA
  have hRB : R B := hK.induced.subset B hKB
  have hAClosed : IsUClosed rules A := hK.induced.closed A hKA
  have hBClosed : IsUClosed rules B := hK.induced.closed B hKB
  have hBIrred : B.Irreducible := hRIrred B hRB
  have hHer : ClosedUHereditary K rules :=
    embeddedClosedHereditary_of_induced
      hK.induced.hereditary hK.iso
  obtain ⟨Z, hZ, C0, hRC0, hArrow0⟩ :=
    hR A B hRA hRB κ
  letI : Finite Z := hZ
  obtain ⟨n, hn, hLocal⟩ := hCutoff B C0 hKB hRC0
  exact coordinated2019_cutoff_one_unrestricted_induced
    (K := K) (rules := rules)
    A B C0 hAClosed hBClosed hBIrred hKB
    (hRIrred C0 hRC0) hHer n hn hLocal κ hArrow0

end AllThoseRamseyClasses.Published
