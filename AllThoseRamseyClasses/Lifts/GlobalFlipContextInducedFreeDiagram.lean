import AllThoseRamseyClasses.Lifts.FullFreeAmalgamClosedContextUnion
import AllThoseRamseyClasses.Lifts.GlobalFlipOuterContextOutside
import PartiteConstruction.Functional.FreeAmalgamClosedInduce

/-!
# The closed outer context is itself a full native free-amalgam diagram

In an ACTUAL full set-valued functional free amalgam
  Whole = Left +_Root Right,
take the whole left piece and a function-closed part SR
of the right side containing the ENTIRE common root. Let
  K = iLeft(Left) union iRight(SR).

The checked union lemma shows K is function-closed in Whole.
The exact free-amalgam outside-context calculation shows:
* the left-side inverse image of K is ALL of Left;
* the right-side inverse image is EXACTLY SR;
* the common-root inverse image is ALL of Root.

Now the already verified full functional closed-induction
theorem constructs a TRUE full native free-amalgam diagram
for the induced structure on K, rather than merely showing K
is a closed vertex set. All original relation and set-valued
function fibres are reflected.

This is a structural prerequisite for treating a transported
outer context under a Claim 2 inner B-only flip as a genuine
rooted extension and eventually proving profile congruence.
It does NOT establish connectedness, minimal separating roots
or equality of the complete rooted incompatibility profiles.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- In a nested full functional free amalgam context retaining the
entire left side and an SR-closed portion of the right side, the
induced side carriers are EXACTLY all of Left and SR of Right.
No right-private vertex outside SR can enter through Left:
full-amalgam overlap would put it in the included common root. -/
theorem fullFreeAmalgam_nestedContext_exactSidePreimages
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
    (hRootR : ∀ r : H, sR r ∈ SR) :
    let K : Set W :=
      iL '' (Set.univ : Set A) ∪ iR '' SR
    (iL ⁻¹' K = Set.univ) ∧ (iR ⁻¹' K = SR) ∧
      ((iL.comp sL) ⁻¹' K = Set.univ) := by
  dsimp only
  let K : Set W := iL '' (Set.univ : Set A) ∪ iR '' SR
  have hLeft : iL ⁻¹' K = (Set.univ : Set A) := by
    ext a
    constructor
    · intro _
      exact Set.mem_univ a
    · intro _
      exact Or.inl ⟨a, Set.mem_univ _, rfl⟩
  have hRight : iR ⁻¹' K = SR := by
    ext b
    constructor
    · intro hbK
      by_contra hbNot
      have hOut : iR b ∉ K :=
        (fullFreeAmalgam_fullLeft_contextOutside_iff
          hFree SR hRootR (iR b)).2 ⟨b, hbNot, rfl⟩
      exact hOut hbK
    · intro hb
      exact Or.inr ⟨b, hb, rfl⟩
  have hRoot : (iL.comp sL) ⁻¹' K =
      (Set.univ : Set H) := by
    ext r
    constructor
    · intro _
      exact Set.mem_univ r
    · intro _
      exact Or.inl ⟨sL r, Set.mem_univ _, rfl⟩
  exact ⟨hLeft, hRight, hRoot⟩

/-- The closure of a root-containing native full-amalgam context
has its OWN genuine full functional free-amalgam decomposition
obtained by restricting the original diagram to this closed
context. All structures are native induced structures with the
complete original function fibres.

The preceding exact-preimage lemma identifies these induced
carriers as Left, the selected closed SR on Right, and Root;
the result is nevertheless stated with canonical induced
subtype carriers to avoid needless non-definitional type casts. -/
theorem fullFreeAmalgam_nestedClosedContext_inducedFreeDiagram
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
    let hK : Whole.IsClosed K :=
      fullFreeAmalgam_closed_union_of_closed_sides
        hFree (Set.univ : Set A) SR
        (by intro F args ha z hz; trivial)
        hSRClosed (fun _ => Set.mem_univ _) hRootR
    let Lset : Set A := iL ⁻¹' K
    let Rset : Set B := iR ⁻¹' K
    let Mset : Set H := (iL.comp sL) ⁻¹' K
    let hL : Left.IsClosed Lset := iL.preimage_isClosed K hK
    let hR : Right.IsClosed Rset := iR.preimage_isClosed K hK
    let hM : Root.IsClosed Mset :=
      (iL.comp sL).preimage_isClosed K hK
    let LS := Left.induce Lset hL
    let RS := Right.induce Rset hR
    let MS := Root.induce Mset hM
    let KS := Whole.induce K hK
    ∃ (mL : Structure.Embedding MS LS)
      (mR : Structure.Embedding MS RS)
      (jL : Structure.Embedding LS KS)
      (jR : Structure.Embedding RS KS),
      Structure.IsFreeAmalgam mL mR jL jR := by
  exact hFree.induceClosed
    (iL '' (Set.univ : Set A) ∪ iR '' SR)
    (fullFreeAmalgam_closed_union_of_closed_sides
      hFree (Set.univ : Set A) SR
      (by intro F args ha z hz; trivial)
      hSRClosed (fun _ => Set.mem_univ _) hRootR)

end AllThoseRamseyClasses.Lifts
