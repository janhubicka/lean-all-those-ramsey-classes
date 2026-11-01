import AllThoseRamseyClasses.Lifts.NamedNestedFunctionalContext
import AllThoseRamseyClasses.Lifts.FreeAmalgamSideIso
import PartiteConstruction.Functional.FreeAmalgamReassociate

/-!
# Extract a native two-stage forbidden test from an actual outer test

Suppose Mid = M +_Start T and the actual forbidden source
Whole = Mid +_Root P, where the outer root Root is embedded
FULLY inside T.  Without assuming either root contains the other:

* the image of T in Mid is closed (since T -> Mid is FULL);
* the union of this T-image and the entire P-image in Whole is
  a genuine closed source substructure Ext;
* Ext has a FULL native source diagram T +_Root P;
* by native reassociation Whole = M +_Start Ext.

This is the forward direction of the equivalence between the
ACTUAL outer-root incompatibility profile and the nested
all-test profile. No forbidden-family isomorphism hypothesis
is needed: the whole source itself stays unchanged.

The reverse direction (from M +_Start (T +_Root P) back to
(M +_Start T) +_Root P) needs the inner-stage restriction and
converse reassociation supplied separately by Tracks B PRs.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- A forbidden FULL functional outer diagram has a literal inner
two-stage decomposition when its ordered outer root factors through
the FULL unchanged T side of the inner diagram.

The existential includes all embeddings and both genuine
`IsFreeAmalgam` certificates. It never replaces a weak forbidden
source map by a supposed injective source quotient. -/
theorem forbiddenOuterFunctionalDiagram_to_nestedTest
    (F : ∀ {W : Type}, Structure L W → Prop)
    {S M T C R P W : Type}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R} {Piece : Structure L P}
    {Whole : Structure L W}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {jMid : Structure.Embedding Mid Whole}
    {jP : Structure.Embedding Piece Whole}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (hOut : Structure.IsFreeAmalgam (iT.comp rT) rP jMid jP)
    (hForbidden : F Whole) :
    ∃ (E : Type) (Ext : Structure L E)
      (jT : Structure.Embedding Tstr Ext)
      (jPext : Structure.Embedding Piece Ext),
      Structure.IsFreeAmalgam rT rP jT jPext ∧
      forbiddenFunctionalDiagram Start F
        ({ Carrier := M, str := Mstr,
           rootEmbedding := sM } : FunctionalRootExtension Start)
        ({ Carrier := E, str := Ext,
           rootEmbedding := jT.comp sT } :
          FunctionalRootExtension Start) := by
  classical
  let SL : Set C := Set.range iT
  have hUniv : Tstr.IsClosed (Set.univ : Set T) := by
    intro Fn args hargs z hz
    exact Set.mem_univ _
  have hSL : Mid.IsClosed SL := by
    simpa only [Set.image_univ] using
      (functionalEmbedding_image_closed Tstr Mid iT
        (Set.univ : Set T) hUniv)
  have hRootInSL : ∀ r : R, (iT.comp rT) r ∈ SL := by
    intro r
    exact ⟨rT r, rfl⟩
  obtain ⟨hK, sLsmall, kT, kP, hExt0,
      hTval, hPval, hRootVal⟩ :=
    fullFreeAmalgam_nestedContext_namedLeftDiagram
      hOut SL hSL hRootInSL
  let incT : Structure.Embedding (Mid.induce SL hSL) Mid :=
    Structure.inclusion Mid SL hSL
  have hRange : ∀ t : T, ∃ z : SL, iT t = incT z := by
    intro t
    exact ⟨⟨iT t, ⟨t, rfl⟩⟩, rfl⟩
  let iTsmall : Structure.Embedding Tstr (Mid.induce SL hSL) :=
    iT.factorThroughClosedRange incT hRange
  have hiTval (t : T) : (iTsmall t).1 = iT t :=
    Structure.Embedding.factorThroughClosedRange_spec
      iT incT hRange t
  have hiTsurj : Function.Surjective iTsmall := by
    intro z
    obtain ⟨t, ht⟩ := z.2
    refine ⟨t, ?_⟩
    apply Subtype.ext
    exact (hiTval t).trans ht
  have hRoot : ∀ r : R, iTsmall (rT r) = sLsmall r := by
    intro r
    apply Subtype.ext
    calc
      (iTsmall (rT r)).1 = iT (rT r) := hiTval (rT r)
      _ = (sLsmall r).1 := (hRootVal r).symm
  let jT : Structure.Embedding Tstr (Whole.induce
      (jP '' (Set.univ : Set P) ∪ jMid '' SL) hK) :=
    kT.comp iTsmall
  let Ext : Structure L
      (jP '' (Set.univ : Set P) ∪ jMid '' SL) :=
    Whole.induce _ hK
  let eExt : Structure.Embedding Ext Whole :=
    Structure.inclusion Whole _ hK
  have hExt : Structure.IsFreeAmalgam rT rP jT kP :=
    freeAmalgam_precompose_left_iso
      hExt0 iTsmall hiTsurj rT hRoot
  have heT (t : T) : eExt (jT t) = jMid (iT t) := by
    change (kT (iTsmall t)).1 = jMid (iT t)
    calc
      (kT (iTsmall t)).1 = jMid (iTsmall t).1 :=
        hTval (iTsmall t)
      _ = jMid (iT t) := congrArg jMid (hiTval t)
  have heP (p : P) : eExt (kP p) = jP p := by
    exact hPval p
  have hRe : Structure.IsFreeAmalgam
      sM (jT.comp sT) (jMid.comp iM) eExt :=
    Structure.IsFreeAmalgam.reassociate_right
      hMid hExt hOut eExt heT heP
  exact ⟨_, Ext, jT, kP, hExt,
    W, Whole, hForbidden, jMid.comp iM, eExt, hRe⟩

end AllThoseRamseyClasses.Lifts
