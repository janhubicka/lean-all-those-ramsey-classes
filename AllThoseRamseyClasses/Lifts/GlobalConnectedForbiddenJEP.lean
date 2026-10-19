import AllThoseRamseyClasses.Lifts.GlobalMaximalTraceJEP
import AllThoseRamseyClasses.Lifts.WeakFreeGaifmanComponents
import AllThoseRamseyClasses.Lifts.EHNFullSideFactor
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Connected forbidden sources and joint embedding over an empty native seam

A connected forbidden source cannot weakly EHN-map across the two
exclusive sides of a genuine native functional free amalgam over an
EMPTY full root. Even a noninjective weak map sends adjacent source
vertices to equal or adjacent target vertices, and no positive
target incidence crosses the two disjoint free sides. Connectivity
therefore forces the entire source image into one side; full-side
factorization then contradicts forbidden-freeness of that side.

This gives native finite JEP whenever every pair of allowed native
finite structures possesses a common FULL empty-root structure.
The latter condition must remain EXPLICIT in functional languages
with nullary functions or relations: empty-root embeddings need
not exist or be compatible. Under this condition and regularity,
the already verified original global maximal-trace JEP transfer
gives expanded-age JEP.

No injectivization, global lift root compatibility or printed
Claim 2 is used. No strong amalgamation or Ramsey statement for
reducible forbidden sources is inferred.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Each genuine finite forbidden structure has a vertex and its
native relationalized Gaifman graph is connected by finite paths.
This excludes an empty forbidden source explicitly. -/
def GlobalForbiddenSourcesConnectedNonempty
    (F : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {U : Type} (Source : Structure L U),
    Finite U → F Source →
    Nonempty U ∧
      ∀ x y : U,
        Relation.ReflTransGen
          (GaifmanAdjacent Source.graph) x y

/-- A free amalgam whose common full native root has EMPTY carrier
avoids all connected nonempty EHN forbidden sources if both sides
avoid them. Weak noninjective forbidden maps are handled directly.

The hypotheses name a true FULL functional free amalgam. Nothing is
assumed about compatibility of canonical lifted relation profiles. -/
theorem avoidsGlobalFunctionalEHN_emptyFreeAmalgam_connected
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    {UX UA UB UT : Type} [IsEmpty UX]
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    {D : Structure L UT}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    {jA : Structure.Embedding A D}
    {jB : Structure.Embedding B D}
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (hA : AvoidsGlobalFunctionalEHN F A)
    (hB : AvoidsGlobalFunctionalEHN F B) :
    AvoidsGlobalFunctionalEHN F D := by
  intro U Source hFin hF f hf
  obtain ⟨⟨base⟩, hConn⟩ := hConnected Source hFin hF
  have hNoRoot (x : U) :
      x ∉ weakFreeRootPart (sL := iA) (iL := jA) f := by
    rintro ⟨r, _⟩
    exact isEmptyElim r
  rcases weakFreePartition_covers hFree f base with
    hRoot | hLeft | hRight
  · exact hNoRoot base hRoot
  · have hAllLeft (x : U) :
        x ∈ weakFreeLeftPart (sL := iA) (iL := jA) f := by
      have hPath := hConn base x
      induction hPath with
      | refl => exact hLeft
      | @tail a b hab hedge ih =>
          exact weakFreePartition_left_step
            hFree f hf.1 ih (hNoRoot b) hedge
    have hRange : ∀ x : U, ∃ a : UA, f x = jA a := by
      intro x
      obtain ⟨⟨a, ha⟩, _⟩ := hAllLeft x
      exact ⟨a, ha⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jA hRange
    exact (hA Source hFin hF g) hg
  · have hAllRight (x : U) :
        x ∈ weakFreeRightPart
          (sL := iA) (iL := jA) (iR := jB) f := by
      have hPath := hConn base x
      induction hPath with
      | refl => exact hRight
      | @tail a b hab hedge ih =>
          exact weakFreePartition_right_step
            hFree f hf.1 ih (hNoRoot b) hedge
    have hRange : ∀ x : U, ∃ b : UB, f x = jB b := by
      intro x
      obtain ⟨⟨b, hb⟩, _⟩ := hAllRight x
      exact ⟨b, hb⟩
    obtain ⟨g, hg, _⟩ :=
      ehnHomomorphismEmbedding_factor_full_side hf jB hRange
    exact (hB Source hFin hF g) hg

/-- Exact compatibility condition on nullary native data needed to
form a common FULL empty substructure of any two finite K-members.
In positive-arity languages this can often be discharged uniformly.
It is NOT automatic for arbitrary nullary relations or functions. -/
def GlobalNativeCommonEmptyRoots
    (K : ∀ {W : Type}, Structure L W → Prop) : Prop :=
  ∀ {UA UB : Type}
    (A : Structure L UA) (B : Structure L UB),
    Finite UA → Finite UB → K A → K B →
    ∃ (UX : Type) (_ : IsEmpty UX) (X : Structure L UX)
      (iA : Structure.Embedding X A)
      (iB : Structure.Embedding X B), True

/-- Connected finite forbidden sources imply FULL finite JEP for
the native forbidden-free class whenever every pair of members
admits a common empty FULL native functional root.

A direct free amalgam is used, not an assumed amalgam of lifts. -/
theorem globalNativeFiniteJEP_connected_of_emptyRoots
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hEmptyRoots : GlobalNativeCommonEmptyRoots
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A)) :
    GlobalNativeFiniteJEP
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) := by
  intro UA UB A B hFinA hFinB hA hB
  obtain ⟨UX, hEmpty, X, iA, iB, _⟩ :=
    hEmptyRoots A B hFinA hFinB hA hB
  letI : IsEmpty UX := hEmpty
  let VD := Structure.FreeAmalgam.Vertex X A B iA iB
  let D : Structure L VD :=
    Structure.FreeAmalgam.amalgam X A B iA iB
  let jA : Structure.Embedding A D :=
    Structure.FreeAmalgam.leftEmbedding X A B iA iB
  let jB : Structure.Embedding B D :=
    Structure.FreeAmalgam.rightEmbedding X A B iA iB
  have hFree : Structure.IsFreeAmalgam iA iB jA jB :=
    Structure.FreeAmalgam.isFreeAmalgam X A B iA iB
  have hAvoidD : AvoidsGlobalFunctionalEHN F D :=
    avoidsGlobalFunctionalEHN_emptyFreeAmalgam_connected
      F hConnected hFree hA hB
  have hFinD : Finite VD := by
    let incl : UA ⊕ UB → VD :=
      fun v => match v with
      | .inl a => jA a
      | .inr b => jB b
    apply Finite.of_surjective incl
    intro x
    rcases hFree.covers x with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact ⟨Sum.inl a, ha.symm⟩
    · exact ⟨Sum.inr b, hb.symm⟩
  exact ⟨VD, D, hFinD, hAvoidD, jA, jB, True.intro⟩

/-- An unconditional (under the genuine nullary/empty-root
compatibility premise) JEP theorem for the original regular global
maximal-trace lift of connected finite forbidden sources. This
discharges the previously explicit native-JEP hypothesis of #504. -/
theorem globalMaximalTraceAge_JEP_connected_of_emptyRoots
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hRegular : GlobalFunctionalPieceRegular F)
    (hConnected : GlobalForbiddenSourcesConnectedNonempty F)
    (hEmptyRoots : GlobalNativeCommonEmptyRoots
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A))
    {VY VZ : Type}
    (Y : Structure (globalFunctionalPieceLanguage F) VY)
    (Z : Structure (globalFunctionalPieceLanguage F) VZ)
    (hY : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Y)
    (hZ : IsGlobalFiniteMaximalTrace F
      (fun {V : Type} (A : Structure L V) =>
        AvoidsGlobalFunctionalEHN F A) Z) :
    ∃ (VT : Type) (T : Structure (globalFunctionalPieceLanguage F) VT),
      IsGlobalFiniteMaximalTrace F
        (fun {V : Type} (A : Structure L V) =>
          AvoidsGlobalFunctionalEHN F A) T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T), True := by
  exact globalFiniteMaximalTraceAge_JEP_of_nativeJEP
    F (fun {V : Type} (A : Structure L V) =>
      AvoidsGlobalFunctionalEHN F A)
    hRegular (globalNativeFiniteJEP_connected_of_emptyRoots
      F hConnected hEmptyRoots) Y Z hY hZ

end AllThoseRamseyClasses.Lifts
