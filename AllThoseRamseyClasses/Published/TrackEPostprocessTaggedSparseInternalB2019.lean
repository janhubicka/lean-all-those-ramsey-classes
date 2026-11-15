import AllThoseRamseyClasses.Published.TrackETaggedInternalBCoverDescent2019
import AllThoseRamseyClasses.Published.TrackEExactKCompletionReconstruction2019
import PartiteConstruction.Iterated.ProjectedBCopyClosedFiniteSaturation

/-!
# Track E: postprocess the ACTUAL second 2019 tagged Picture by closed B saturation

English proof of the interface:
- First strict profile sparsening P already has a Ramsey arrow,
  exact small profile Bplus-tree completions and INTERNAL Bplus-copy
  extensions of all irreducibles.
- Canonical fresh tagging transfers the latter to the SAME Ptag and
  proves Btag ordinarily hereditarily irreducible (the verified first
  profile base lemma).
- The second 2019 protected Picture Q is U-closed in the TAG language,
  has external U-closed irreducible Btag test coverage, a FULL Ramsey
  arrow, and ONE selected ordinary HE q:Q→Ptag.
- Attach full Btag-copies over U-CLOSED HULLS of the exact ordinary
  irreducible core tests, using the verified-candidate local finite
  saturation construction. It yields Qnew with a full inclusion Q↪Qnew,
  SAME q on old vertices, U-closedness, external protected Btag coverage,
  and INTERNAL Btag extensions. The Ramsey arrow persists.
- Do NOT try to carry individual weak K-completion targets across each
  free attachment. Instead reconstruct them for EVERY exact small
  S⊆Qnew, by the already verified first-stage local tree certificates
  and the SAME selected Qnew→Ptag HE. This retains original cutoff n,
  without enlarging or closing any small test.
- Forget tagged/profile relations in internal copies to obtain actual
  internal Base copies of the ORIGINAL reduct on the SAME final carrier.

This theorem packages a genuine RELATIONAL tagged POSTPROCESSING step.
It does not identify the new final tag source as a canonical whole-mask
Option(Set) encoding, does not assert class membership of the final
native witness, and does not prove strict full native B-tree locality.
Those remain independent endgame obligations.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.RelStructure.ProjectedBCopyControl

universe u v
variable {L : RelLanguage.{u}}

/-- One simultaneous 2019 tagged witness with original selected control
HE, exact small weak K-completions, preserved Ramsey arrow, protected
external tagged B coverage and genuine INTERNAL tagged and original B
copy extensions. All conclusion clauses concern the SAME Qnew.

The new witness is obtained by saturating an ACTUAL second-stage Q,
not by switching to the independent native EHN construction. -/
theorem profile2019_postprocess_tagged_sparse_with_internalB
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UB VP VQ VA : Type v}
    [Finite UB] [Finite VP] [Finite VQ]
    (Base : RelStructure L UB)
    (hBase : IsUClosed rules Base)
    (hBK : K Base)
    (hClosed : ∀ {X : Type v} (E : RelStructure L X),
      K E → IsUClosed rules E)
    (hHer : ClosedUHereditary K rules)
    (hStrong : HasFiniteStrongAmalgamation K)
    (hKIrr : ∀ {X : Type v} (E : RelStructure L X),
      K E → E.Irreducible)
    (P : RelStructure (closureProfileLanguage2019 rules Base) VP)
    (n : ℕ)
    (hLocalP : ∀ T : Finset VP, T.card ≤ n →
      HasTreeCompletion
        (closureProfileExpansion2019 rules Base Base)
        (P.induce (↑T : Set VP)))
    (hInternalP :
      IrreduciblesExtendTo
        (closureProfileExpansion2019 rules Base Base) P)
    (A : RelStructure (profileRootTagLanguage2019 rules Base) VA)
    (Q : RelStructure (profileRootTagLanguage2019 rules Base) VQ)
    (hQClosed : IsUClosed (profileRootTagRules2019 rules Base) Q)
    (hQCover : ∀ {X : Type v}
      (Test : RelStructure (profileRootTagLanguage2019 rules Base) X),
      IsUClosed (profileRootTagRules2019 rules Base) Test →
      IsUIrreducible (profileRootTagRules2019 rules Base) Test →
      Embedding Test Q →
      Nonempty (Embedding Test (profileTaggedCanonical2019 rules Base Base)))
    (q : VQ → VP)
    (hQHE : Q.IsHomomorphismEmbedding
      (profileRootTagExpansion2019 rules Base P) q)
    (Color : Type*)
    (hArrow : StructuralRamsey.Arrow A
      (profileTaggedCanonical2019 rules Base Base) Q Color) :
    ∃ (W : Type v) (_ : Finite W)
      (Qnew : RelStructure (profileRootTagLanguage2019 rules Base) W)
      (j : Embedding Q Qnew) (qNew : W → VP),
      IsUClosed (profileRootTagRules2019 rules Base) Qnew ∧
      Qnew.IsHomomorphismEmbedding
        (profileRootTagExpansion2019 rules Base P) qNew ∧
      (∀ x : VQ, qNew (j x) = q x) ∧
      (∀ {X : Type v}
        (Test : RelStructure (profileRootTagLanguage2019 rules Base) X),
        IsUClosed (profileRootTagRules2019 rules Base) Test →
        IsUIrreducible (profileRootTagRules2019 rules Base) Test →
        Embedding Test Qnew →
        Nonempty (Embedding Test (profileTaggedCanonical2019 rules Base Base))) ∧
      IrreduciblesExtendTo
        (profileTaggedCanonical2019 rules Base Base) Qnew ∧
      IrreduciblesExtendTo Base (profileRootTagOriginal2019 Base Qnew) ∧
      (∀ S : Finset W, S.card ≤ n →
        HasInducedClosedUKCompletion K rules
          ((profileRootTagOriginal2019 Base Qnew).induce
            (↑S : Set W))) ∧
      StructuralRamsey.Arrow A
        (profileTaggedCanonical2019 rules Base Base) Qnew Color := by
  classical
  let Bplus := closureProfileExpansion2019 rules Base Base
  let Btag := profileTaggedCanonical2019 rules Base Base
  let Ptag := profileRootTagExpansion2019 rules Base P
  have hBtagClosed :
      IsUClosed (profileRootTagRules2019 rules Base) Btag :=
    profileRootTag2019_closed_canonical Base Bplus hBase
  have hBtagHered : HereditarilyIrreducible Btag :=
    profileTaggedCanonical2019_base_hereditarilyIrreducible Base hBase
  have hPtagInternal : IrreduciblesExtendTo Btag Ptag :=
    profileRootTag2019_internalBCover_of_old Base Bplus P hInternalP
  letI : Fintype VQ := Fintype.ofFinite VQ
  obtain ⟨W, hW, Qnew, j, qNew, hQnewClosed, hQnewHE, hQnewOldMap,
      hQnewCover, hQnewInternal⟩ :=
    ProjectedBCopyControl.build_closed_all
      Q Btag Ptag q hQClosed hBtagClosed hQCover
      hBtagHered hQHE hPtagInternal
  letI : Finite W := hW
  have hOriginalInternal :
      IrreduciblesExtendTo Base (profileRootTagOriginal2019 Base Qnew) :=
    profileRootTag2019_internalOriginalBCover_of_tagged
      Base Qnew hQnewInternal
  have hSmallK : ∀ S : Finset W, S.card ≤ n →
      HasInducedClosedUKCompletion K rules
        ((profileRootTagOriginal2019 Base Qnew).induce
          (↑S : Set W)) :=
    profile2019_exactWeak_K_completions_of_protected_taggedHE
      Base hBase hBK hClosed hHer hStrong hKIrr
      P n hLocalP Qnew hQnewClosed hQnewCover qNew hQnewHE
  have hArrowNew :
      StructuralRamsey.Arrow A Btag Qnew Color :=
    hArrow.of_embedding j
  exact ⟨W, hW, Qnew, j, qNew, hQnewClosed, hQnewHE,
    hQnewOldMap, hQnewCover, hQnewInternal, hOriginalInternal,
    hSmallK, hArrowNew⟩

end AllThoseRamseyClasses.Published
