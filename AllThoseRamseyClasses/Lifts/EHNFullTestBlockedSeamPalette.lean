import AllThoseRamseyClasses.Lifts.EHNPairwiseSourceTestRootInjectivity

/-!
# Track D: genuine full-native irreducible-test restrictions on one-vertex seam moves

The preceding occupied-seam counting argument is purely numerical.
Even when moving an original source vertex a to an occupied target
seam point d lowers the number of original source collision pairs,
the new map may not be EHN.

Here we give a SOURCE-GEOMETRIC, map-independent obstruction.
A target image d is TEST-BLOCKED for a by an old map f when
d=f(b) for some b≠a which lies together with a in a genuine
full irreducible source test. Recolouring a to such a value d
makes that ACTUAL test impossible to embed FULLY into the target:
it would identify two distinct vertices of one full source test.

Thus every original EHN-preserving one-vertex seam recolouring
must choose a new image OUTSIDE the set of test-blocked values.
If all other seam points are blocked, no seam-only change of a
can preserve EHN -- a precise failure of the tempting local
collision-splitting strategy even before positive relation or
set-valued native function checks are considered.

No global injectivity, closure of the forbidden family under
quotients, invented canonical relation, or arbitrary source
replacement is involved. This is not unrestricted Section 3
Claim 1, Claim 2, or strong amalgamation.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- For a fixed ORIGINAL source vertex a and map f, a target
point d is blocked precisely when some distinct original
source vertex b of image d lies WITH a in a common genuine
FULL native irreducible source test. We use original source
vertices and full embeddings, not an incidence quotient. -/
def nativeFullTestBlockedTargetImages
    {V UT : Type} (Source : Structure L V)
    (f : V → UT) (a : V) : Set UT :=
  f '' {b : V |
    a ≠ b ∧
    ∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        ∃ x y : X, e x = a ∧ e y = b}

/-- A BLOCKED destination gives an actual specific FULL
irreducible embedded original source test which CANNOT have
the target coordinates prescribed by the candidate recolouring.

This is stronger than abstract non-EHN: it supplies the exact
genuine test e:E↪Source witnessing the failure. The original
map f itself need not be EHN. -/
theorem oneVertexRecolor_blockedTarget_has_explicitFailedFullTest
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT) (a : V) (d : UT)
    (hBlocked : d ∈ nativeFullTestBlockedTargetImages Source f a) :
    ∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        (∃ x : X, e x = a) ∧
        ¬ ∃ ge : Structure.Embedding E Target,
          ∀ x : X, ge x =
            (fun z : V => if z = a then d else f z) (e x) := by
  rcases hBlocked with ⟨b, hb, hFb⟩
  rcases hb with ⟨hab, X, E, hIr, e, x, y, hx, hy⟩
  refine ⟨X, E, hIr, e, ⟨x, hx⟩, ?_⟩
  rintro ⟨ge, hge⟩
  have hxy : x ≠ y := by
    intro hxy
    exact hab (hx.symm.trans ((congrArg e hxy).trans hy))
  have hEq : ge x = ge y := by
    calc
      ge x =
          (fun z : V => if z = a then d else f z) (e x) := hge x
      _ = d := by rw [hx]; simp
      _ = f b := hFb.symm
      _ = (fun z : V => if z = a then d else f z) (e y) := by
        rw [hy]
        simp [hab.symm]
      _ = ge y := (hge y).symm
  exact hxy (ge.injective hEq)

/-- Every genuine FULL-test-preserving EHN one-vertex recolouring
must avoid ALL blocked original source-test neighbour images.
The old map need not itself be EHN; this is a necessary condition
on the proposed new map. -/
theorem oneVertexRecolor_EHN_avoids_fullTestBlockedTargetImages
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT) (a : V) (d : UT)
    (hNewEHN : Source.IsEHNHomomorphismEmbedding Target
      (fun z : V => if z = a then d else f z)) :
    d ∉ nativeFullTestBlockedTargetImages Source f a := by
  intro hBlocked
  obtain ⟨X, E, hIr, e, _ha, hNoFullTest⟩ :=
    oneVertexRecolor_blockedTarget_has_explicitFailedFullTest
      Source Target f a d hBlocked
  exact hNoFullTest (hNewEHN.2 E hIr e)

/-- Test-blocked seam saturation: if every seam value OTHER
than the current image f(a) is the image of some source vertex
linked to a by a common FULL irreducible original source test,
then no NONTRIVIAL seam-only one-vertex recolouring can be EHN.

The source may have functions of arbitrary arity, with genuinely
set-valued outputs. Their additional preservation constraints
are not needed for this particular impossibility. -/
theorem oneVertexRecolor_noNontrivialEHN_while_fullTestSeamSaturated
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT) (a : V) (Seam : Set UT)
    (hSeamTestSaturated :
      ∀ d : UT, d ∈ Seam → d ≠ f a →
        d ∈ nativeFullTestBlockedTargetImages Source f a) :
    ∀ d : UT, d ∈ Seam → d ≠ f a →
      ¬ Source.IsEHNHomomorphismEmbedding Target
        (fun z : V => if z = a then d else f z) := by
  intro d hd hDifferent hNewEHN
  exact (oneVertexRecolor_EHN_avoids_fullTestBlockedTargetImages
    Source Target f a d hNewEHN)
    (hSeamTestSaturated d hd hDifferent)


/-- The PAIR-INJECTIVITY fragment of native full-test preservation:
a map must separate any two distinct original source vertices
which occur together in some FULL irreducible original source
test. This condition is necessary but NOT sufficient for EHN:
full target test embeddings also reflect relations and entire
native function fibres. -/
def SeparatesJointIrreducibleSourceTestPairs
    {V UT : Type} (Source : Structure L V) (f : V → UT) : Prop :=
  ∀ (a b : V), a ≠ b →
    (∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        ∃ x y : X, e x = a ∧ e y = b) →
      f a ≠ f b

/-- An ACTUAL EHN homomorphism-embedding separates every
pair belonging to one irreducible source test, independent of
root image injection, forbidden-family image closure, or
additional native function-input coverage. -/
theorem ehn_separates_jointIrreducibleSourceTestPairs
    {V UT : Type}
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (hf : Source.IsEHNHomomorphismEmbedding Target f) :
    SeparatesJointIrreducibleSourceTestPairs Source f := by
  intro a b hab hTest hSame
  exact (ehn_collidingSourcePair_not_in_jointIrreducibleTest
    Source Target f hf a b hab hSame) hTest

/-- EXACT necessary-and-sufficient one-vertex palette test for
the PAIR-INJECTIVITY fragment of full native source-test
preservation. If the old map f separates all pairs of original
vertices occurring jointly in full irreducible tests, then
the candidate map changing just a to d continues to separate
all such pairs IFF d is NOT a blocked old test-neighbour image.

This does NOT conclude preservation of entire full native tests;
the old relation/function/reflection conditions are separate. -/
theorem oneVertexRecolor_jointTestPairSeparation_iff_notBlocked
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (f : V → UT)
    (hf : SeparatesJointIrreducibleSourceTestPairs Source f)
    (a : V) (d : UT) :
    SeparatesJointIrreducibleSourceTestPairs Source
      (fun z : V => if z = a then d else f z) ↔
      d ∉ nativeFullTestBlockedTargetImages Source f a := by
  constructor
  · intro hNew hBlocked
    rcases hBlocked with ⟨b, ⟨hab, X, E, hIr, e, x, y, hx, hy⟩, hFb⟩
    have hb : b ≠ a := hab.symm
    have hSame :
        (fun z : V => if z = a then d else f z) a =
        (fun z : V => if z = a then d else f z) b := by
      simp [hb, hFb]
    exact (hNew a b hab
      ⟨X, E, hIr, e, x, y, hx, hy⟩) hSame
  · intro hNotBlocked
    intro x y hxy hTest hSame
    rcases hTest with ⟨X, E, hIr, e, u, v, hu, hv⟩
    by_cases hxa : x = a
    · subst x
      have hya : y ≠ a := hxy.symm
      have hd : d = f y := by
        simpa [hya] using hSame
      apply hNotBlocked
      exact ⟨y, ⟨hxy, X, E, hIr, e, u, v, hu, hv⟩, hd.symm⟩
    · by_cases hya : y = a
      · subst y
        have hd : f x = d := by
          simpa [hxa] using hSame
        apply hNotBlocked
        exact ⟨x, ⟨hxy.symm, X, E, hIr, e, v, u, hv, hu⟩, hd⟩
      · have hOldSame : f x = f y := by
          simpa [hxa, hya] using hSame
        exact (hf x y hxy
          ⟨X, E, hIr, e, u, v, hu, hv⟩) hOldSame


/-- A FULL native embedding of the old source into a replacement
preserves all blocked image values for original source vertices
when the target map agrees on that embedded old source.

Every old irreducible source test E↪Old composes with the full
embedding Old↪New to a genuine full test E↪New. Consequently,
a blocked value cannot become unblocked merely by adding new
vertices, relations or native function values while retaining
the whole OLD source as a full embedded copy with its map fixed.

A collision-tolerant repair must instead change the relevant
old test/profile, change target coordinates on more vertices,
or use a different source piece; this theorem does not construct
any such repair. -/
theorem fullNativeSourceEmbedding_preserves_testBlockedTargetImages
    {V W UT : Type}
    (Old : Structure L V) (New : Structure L W)
    (iOld : Structure.Embedding Old New)
    (fOld : V → UT) (fNew : W → UT)
    (hOldTarget : ∀ v : V, fNew (iOld v) = fOld v)
    (a : V) :
    nativeFullTestBlockedTargetImages Old fOld a ⊆
      nativeFullTestBlockedTargetImages New fNew (iOld a) := by
  rintro d ⟨b, ⟨hab, X, E, hIr, e, x, y, hx, hy⟩, hImage⟩
  have hNotEq : iOld a ≠ iOld b := by
    intro hEq
    exact hab (iOld.injective hEq)
  let eNew : Structure.Embedding E New := iOld.comp e
  have hxNew : eNew x = iOld a := by
    change iOld (e x) = iOld a
    exact congrArg iOld.toFun hx
  have hyNew : eNew y = iOld b := by
    change iOld (e y) = iOld b
    exact congrArg iOld.toFun hy
  exact ⟨iOld b, ⟨hNotEq, X, E, hIr,
      eNew, x, y, hxNew, hyNew⟩,
    (hOldTarget b).trans hImage⟩

/-- In particular, a genuinely blocked target value remains
inadmissible under ANY full native source extension retaining
the old map on the original source: changing only the image of
iOld(a) to that blocked value can never give an EHN map of New.

This prevents an invalid shortcut which proposes to fix an
irreducible-test collision by freely enlarging an unchanged
original embedded source. The conditional replacement may still
change the native source structure itself or multiple target
coordinates -- neither is ruled out here. -/
theorem fullNativeSourceExtension_blockedValue_prevents_EHN_recolor
    {V W UT : Type} [DecidableEq W]
    (Old : Structure L V) (New : Structure L W)
    (Target : Structure L UT)
    (iOld : Structure.Embedding Old New)
    (fOld : V → UT) (fNew : W → UT)
    (hOldTarget : ∀ v : V, fNew (iOld v) = fOld v)
    (a : V) (d : UT)
    (hOldBlocked :
      d ∈ nativeFullTestBlockedTargetImages Old fOld a) :
    ¬ New.IsEHNHomomorphismEmbedding Target
      (fun z : W => if z = iOld a then d else fNew z) := by
  intro hNewEHN
  have hStillBlocked :
      d ∈ nativeFullTestBlockedTargetImages New fNew (iOld a) :=
    fullNativeSourceEmbedding_preserves_testBlockedTargetImages
      Old New iOld fOld fNew hOldTarget a hOldBlocked
  exact (oneVertexRecolor_EHN_avoids_fullTestBlockedTargetImages
    New Target fNew (iOld a) d hNewEHN) hStillBlocked


/-- A FULL native source extension retains pairwise source-test
coverage on the literal embedded old set: witnesses for distinct
old vertices are transported by composing their original FULL
irreducible tests with the embedding Old↪New.

This preserves the hypotheses of the already verified original
geometric-root injectivity gate when a source-changing
construction genuinely keeps an old subsource fully embedded.
Neither weak positive maps nor an arbitrary quotient suffice. -/
theorem fullNativeSourceEmbedding_preserves_pairwiseIrredTestCover
    {V W : Type}
    (Old : Structure L V) (New : Structure L W)
    (iOld : Structure.Embedding Old New)
    (S : Set V)
    (hCover : PairwiseIrreducibleSourceTestCover Old S) :
    PairwiseIrreducibleSourceTestCover New (iOld '' S) := by
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hab
  have hxy : x ≠ y := by
    intro h
    exact hab (congrArg iOld.toFun h)
  obtain ⟨X, E, hIr, e, u, v, hu, hv⟩ :=
    hCover x hx y hy hxy
  let eNew : Structure.Embedding E New := iOld.comp e
  have huNew : eNew u = iOld x := by
    change iOld (e u) = iOld x
    exact congrArg iOld.toFun hu
  have hvNew : eNew v = iOld y := by
    change iOld (e v) = iOld y
    exact congrArg iOld.toFun hv
  exact ⟨X, E, hIr, eNew, u, v, huNew, hvNew⟩

end AllThoseRamseyClasses.Lifts
