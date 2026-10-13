import AllThoseRamseyClasses.Published.ClosedKRootTwoSide2019
import PartiteConstruction.Ramsey.ClosureMaximalWeakRank

/-!
# The literal root of a CLOSED MAXIMAL source is closed;
# if irreducible, original B-coverage puts it in K

The two-REST native closed-K-root completion lemma needs its
literal common induced source ROOT to be U-CLOSED and in K.
This is NOT automatic for arbitrary exact WEAK sources: a weak
test can omit outputs of closure rules, and an arbitrary core
root can be ordinary reducible.

For a stronger but honest special source hypothesis the root
condition becomes provable without inventing a K-boundary:

(1) When the FULL exact source F is intrinsically U-CLOSED and
    has MAXIMAL intrinsic generating rank USize(F)=|F|,
    EVERY induced vertex subset S of F is relatively U-closed
    by the checked maximal-rank independence theorem.
    Intrinsic closedness of F then makes F|S intrinsically
    U-CLOSED. There is no replacement of S by a hull.

(2) If that literal induced source ROOT F|S is ALSO ORDINARY
    IRREDUCIBLE, it is U-irreducible; the original corrected
    closed-irreducible-copy coverage of F by B in K gives
    a full embedding F|S -> B. Closed heredity of K
    proves F|S itself belongs to K.

The ordinary irreducibility premise is explicit and not
known for all native core REST separators. The theorem
does NOT apply to arbitrary NONCLOSED weak sources or
deduce completion of general higher-rank tests. It
supplies a concrete sufficient condition for the
CI-green restricted closed-K-root gluing criterion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A CLOSED finite structure of MAXIMAL intrinsic U-generating
rank has EVERY induced subset intrinsically U-CLOSED.

This needs both hypotheses. Maximal rank of a NONCLOSED weak
test alone does not imply intrinsic closedness of its subsets. -/
theorem native2019_closed_maximal_source_all_induced_UClosed
    {rules : ClosureDescription L}
    {U : Type v} [Fintype U]
    (F : RelStructure L U)
    (hFClosed : IsUClosed rules F)
    (hMax : USize rules F = Fintype.card U)
    (S : Set U) :
    IsUClosed rules (F.induce S) :=
  hFClosed.induce_of_USubstructure S
    ((all_subsets_relative_of_USize_eq_card rules F hMax) S)

/-- If an arbitrary literal induced root of a CLOSED MAXIMAL
finite source is ORDINARY IRREDUCIBLE, and the full source
has the ORIGINAL closed irreducible B-copy coverage,
the root is itself a CLOSED K-member.

The fixed B is in K; the root need not be the selected A,
and its size is not assumed small. -/
theorem native2019_closed_maximal_irreducible_root_is_K
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {U V : Type v} [Fintype U]
    (F : RelStructure L U)
    (B : RelStructure L V)
    (hFClosed : IsUClosed rules F)
    (hMax : USize rules F = Fintype.card U)
    (hBK : K B)
    (hHer : ClosedUHereditary K rules)
    (hCover : ∀ {X : Type v} (Test : RelStructure L X),
      IsUClosed rules Test →
      IsUIrreducible rules Test →
      Embedding Test F →
      Nonempty (Embedding Test B))
    (S : Set U)
    (hIrred : (F.induce S).Irreducible) :
    IsUClosed rules (F.induce S) ∧ K (F.induce S) := by
  have hRootClosed : IsUClosed rules (F.induce S) :=
    native2019_closed_maximal_source_all_induced_UClosed
      F hFClosed hMax S
  have hRootUIrred : IsUIrreducible rules (F.induce S) :=
    hIrred.isUIrreducible rules
  obtain ⟨e⟩ :=
    hCover (F.induce S) hRootClosed hRootUIrred
      (inclusion F S)
  have hKRoot : K (F.induce S) :=
    hHer (F.induce S) B hBK hRootClosed e
  exact ⟨hRootClosed, hKRoot⟩

end AllThoseRamseyClasses.Published
