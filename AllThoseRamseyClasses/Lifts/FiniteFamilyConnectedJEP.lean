import AllThoseRamseyClasses.Lifts.ConnectedSourceEmptyRootFactor
import AllThoseRamseyClasses.Lifts.FiniteFamilyMaximalTraceJEP
import AllThoseRamseyClasses.Lifts.GlobalConnectedPositiveArityJEP
import PartiteConstruction.Functional.FullFreeAmalgam

/-!
# Connected forbidden families: JEP for finite folded maximal-trace ages

The finite-family folded all-closed-component construction already has
full strong amalgamation, a hereditary age, genuine finite expansion
fibres, and a conditional full JEP theorem. The one remaining premise
of that JEP theorem is FULL joint embedding of its original native
forbidden-free class.

A family of finite, nonempty, Gaifman-connected native sources avoids
this obstruction if two native allowed structures have a common FULL
empty root. Indeed, any possibly noninjective EHN source witness in the
empty-root free amalgam must factor through an entire side, contradicting
avoidance of that side. The reusable source-specific factorization is
in ConnectedSourceEmptyRootFactor. There is NO need to assume the
forbidden sources are irreducible.

If all original relation and function arities are positive, the empty
root exists and embeds fully in EVERY native structure. Therefore the
actual finite-family maximal-trace age has JEP automatically in that
important case. Nullary symbols require their original compatibility
hypothesis; no unconditional empty-root assertion is made for them.

Strong amalgamation for this folded finite-family age was previously
verified, but the RAMSEY property and the original printed regular
infinite-family strong-amalgamation lemma are still distinct open
obligations. All complete old function-value fibres are preserved.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Each named forbidden source is nonempty and connected under its
actual native function-graph Gaifman adjacency. No irreducibility,
root-injectivity or family-image-closure premise is included. -/
def FiniteNamedSourcesConnectedNonempty
    (Family : FiniteNamedFunctionalSources.{u,0} L) : Prop :=
  ∀ i : Family.Index,
    Nonempty (Family.Carrier i) ∧
      ∀ x y : Family.Carrier i,
        Relation.ReflTransGen
          (GaifmanAdjacent (Family.source i).graph) x y

/-- The native free amalgam of two structures avoiding the named
connected sources still avoids them if their common FULL native
functional root is empty. This uses a real EHN factorization and
works even when a forbidden-source map is globally noninjective. -/
theorem avoidsFiniteNamedEHN_emptyFreeAmalgam_connected
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hConnected : FiniteNamedSourcesConnectedNonempty Family)
    {UX UA UB UT : Type} [IsEmpty UX]
    {X : Structure L UX}
    {A : Structure L UA} {B : Structure L UB}
    {D : Structure L UT}
    {iA : Structure.Embedding X A}
    {iB : Structure.Embedding X B}
    {jA : Structure.Embedding A D}
    {jB : Structure.Embedding B D}
    (hFree : Structure.IsFreeAmalgam iA iB jA jB)
    (hA : AvoidsFiniteNamedEHN Family A)
    (hB : AvoidsFiniteNamedEHN Family B) :
    AvoidsFiniteNamedEHN Family D := by
  intro i f hf
  rcases connectedSourceEHN_factor_emptyFreeSide
      (Family.source i) (hConnected i).1 (hConnected i).2
      X A B D iA iB jA jB hFree f hf with
    ⟨g, hg⟩ | ⟨g, hg⟩
  · exact (hA i g) hg
  · exact (hB i g) hg

/-- The native finite named forbidden-free class has full joint
embedding whenever its finite members share compatible FULL empty
roots and all named forbidden sources are nonempty and connected.
The conclusion is a real finite native functional free amalgam. -/
theorem finiteNamedNativeFiniteJEP_connected_of_emptyRoots
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hConnected : FiniteNamedSourcesConnectedNonempty Family)
    (hEmptyRoots : GlobalNativeCommonEmptyRoots
      (fun {V : Type} (A : Structure L V) =>
        AvoidsFiniteNamedEHN Family A)) :
    FiniteNamedNativeFiniteJEP Family := by
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
  have hAvoidD : AvoidsFiniteNamedEHN Family D :=
    avoidsFiniteNamedEHN_emptyFreeAmalgam_connected
      Family hConnected hFree hA hB
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

/-- Native finite JEP transfers to the actual hereditary folded
maximal-trace age. Its strong amalgamation was proved separately;
neither AP nor Ramsey is assumed by this JEP argument. -/
theorem finiteNamedMaximalTraceAge_JEP_connected_of_emptyRoots
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hConnected : FiniteNamedSourcesConnectedNonempty Family)
    (hEmptyRoots : GlobalNativeCommonEmptyRoots
      (fun {V : Type} (A : Structure L V) =>
        AvoidsFiniteNamedEHN Family A))
    {VY VZ : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VY)
    (Z : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VZ)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (hZ : IsFiniteNamedMaximalTrace Family Z) :
    ∃ (VT : Type)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T), True := by
  exact finiteNamedMaximalTraceAge_JEP_of_nativeJEP
    Family
    (finiteNamedNativeFiniteJEP_connected_of_emptyRoots
      Family hConnected hEmptyRoots) Y Z hY hZ

/-- In a positive-arity native language, all pairs of structures
have the SAME fully embedded empty root. This eliminates the
remaining native-JEP hypothesis for connected finite named families. -/
theorem finiteNamedNativeFiniteJEP_connected_positiveArity
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : FiniteNamedSourcesConnectedNonempty Family) :
    FiniteNamedNativeFiniteJEP Family :=
  finiteNamedNativeFiniteJEP_connected_of_emptyRoots
    Family hConnected
    (nativeCommonEmptyRoots_of_positiveArity L hArity
      (fun {V : Type} (A : Structure L V) =>
        AvoidsFiniteNamedEHN Family A))

/-- Genuine full joint embedding of the finite-family folded
maximal-trace age when every named forbidden source is nonempty
and connected and the original language has only positive arities.
Together with existing strong AP and finite fibres, this completes
its age/JEP/strong-AP/precompactness structural package, but NOT
a Ramsey theorem. -/
theorem finiteNamedMaximalTraceAge_JEP_connected_positiveArity
    (Family : FiniteNamedFunctionalSources.{u,0} L)
    (hArity : NativeLanguagePositiveArity L)
    (hConnected : FiniteNamedSourcesConnectedNonempty Family)
    {VY VZ : Type}
    (Y : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VY)
    (Z : Structure
      (functionalLiftLanguageBig L Family.ComponentTag
        (fun tag => tag.width Family)) VZ)
    (hY : IsFiniteNamedMaximalTrace Family Y)
    (hZ : IsFiniteNamedMaximalTrace Family Z) :
    ∃ (VT : Type)
      (T : Structure
        (functionalLiftLanguageBig L Family.ComponentTag
          (fun tag => tag.width Family)) VT),
      IsFiniteNamedMaximalTrace Family T ∧
      ∃ (jY : Structure.Embedding Y T)
        (jZ : Structure.Embedding Z T), True := by
  exact finiteNamedMaximalTraceAge_JEP_of_nativeJEP
    Family
    (finiteNamedNativeFiniteJEP_connected_positiveArity
      Family hArity hConnected) Y Z hY hZ

end AllThoseRamseyClasses.Lifts
