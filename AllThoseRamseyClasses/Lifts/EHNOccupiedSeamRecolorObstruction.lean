import AllThoseRamseyClasses.Lifts.EHNPairwiseSourceTestRootInjectivity
import AllThoseRamseyClasses.Lifts.EHNSetwiseLocalRecolorVerification

/-!
# Track D: occupied-seam recolouring and the native irreducible-test obstruction

For the ORIGINAL finite forbidden-source map f : V → Target, move
one source vertex a to a target seam point d, which may already
have preimages under f. This is a genuinely new case not covered
by the "globally unused seam point" counting lemma.

Every NEW collision with a has a source partner in the old
d-fibre. All untouched pairs retain their old collision status.
More importantly, a proposed NEW EHN map cannot identify a with
an old d-fibre source vertex b whenever a,b occur together in a
FULL original native irreducible test. In particular a pairwise
test-covered selected root cannot undergo an occupied-target
recolouring that collapses two of its source root vertices.

These source-test obstructions are unconditional necessary
criteria and are NOT claims that the recolouring exists as EHN.
The forbidden source is unchanged; no quotient, added canonical
relation, or unsupported native function truncation is used.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- When one ORIGINAL source vertex a is recoloured to d,
all genuine ordered collision pairs not involving a keep
their exact original collision status, including seam membership. -/
theorem oneVertexRecolor_untouchedSeamPairs_iff
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT)
    (a : V) (d : UT)
    (x y : V) (hx : x ≠ a) (hy : y ≠ a) :
    (x ≠ y ∧
      (fun z : V => if z = a then d else f z) x =
        (fun z : V => if z = a then d else f z) y ∧
      (fun z : V => if z = a then d else f z) x ∈ Seam) ↔
    (x ≠ y ∧ f x = f y ∧ f x ∈ Seam) := by
  simp [hx, hy]

/-- For a distinct ORIGINAL source partner b, a one-vertex
recolouring to d creates a distinct-source ordered seam
collision (a,b) exactly when the old map had f(b)=d.

No global freshness hypothesis on d is used or available. -/
theorem oneVertexRecolor_firstSeamPair_iff_occupiedFibre
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT)
    (a b : V) (hab : a ≠ b)
    (d : UT) (hd : d ∈ Seam) :
    (a ≠ b ∧
      (fun z : V => if z = a then d else f z) a =
        (fun z : V => if z = a then d else f z) b ∧
      (fun z : V => if z = a then d else f z) a ∈ Seam) ↔
    f b = d := by
  have hb : b ≠ a := Ne.symm hab
  simp only [if_pos rfl, if_neg hb]
  constructor
  · intro h
    exact h.2.1.symm
  · intro h
    exact ⟨hab, h.symm, hd⟩

/-- For the other orientation (b,a), the same occupied
old d-fibre gives exactly the new seam collisions. -/
theorem oneVertexRecolor_secondSeamPair_iff_occupiedFibre
    {V UT : Type} [DecidableEq V]
    (f : V → UT) (Seam : Set UT)
    (a b : V) (hab : a ≠ b)
    (d : UT) (hd : d ∈ Seam) :
    (b ≠ a ∧
      (fun z : V => if z = a then d else f z) b =
        (fun z : V => if z = a then d else f z) a ∧
      (fun z : V => if z = a then d else f z) b ∈ Seam) ↔
    f b = d := by
  have hb : b ≠ a := Ne.symm hab
  simp only [if_pos rfl, if_neg hb]
  constructor
  · intro h
    exact h.2.1
  · intro h
    exact ⟨hab.symm, h, h ▸ hd⟩

/-- An occupied seam target point d cannot be used as the new
image of a if another ORIGINAL source vertex b already maps to
d and a,b lie together in a genuine FULL irreducible source test.

The NEW candidate map is not required to be positive on old
relations or functions; failure of the full-test EHN clause is
already enough. -/
theorem oneVertexRecolor_toOccupiedImage_EHN_forces_jointTestGap
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (a b : V) (hab : a ≠ b)
    (d : UT) (hOccupied : f b = d)
    (hNewEHN : Source.IsEHNHomomorphismEmbedding Target
      (fun z : V => if z = a then d else f z)) :
    ¬ ∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Source,
        ∃ x y : X, e x = a ∧ e y = b := by
  have hSame :
      (fun z : V => if z = a then d else f z) a =
      (fun z : V => if z = a then d else f z) b := by
    simp [hab.symm, hOccupied]
  exact ehn_collidingSourcePair_not_in_jointIrreducibleTest
    Source Target
    (fun z : V => if z = a then d else f z)
    hNewEHN a b hab hSame

/-- Stronger positive obstruction for a genuine pairwise
irreducible-test-covered ORIGINAL source set S: recolouring a
to an occupied image of another source vertex b in S cannot
remain EHN. In particular this excludes occupied-fibre splits
that introduce a collision inside an already covered selected
geometric separator root.

Unlike old root-image injection, this impossibility does not
need the old map to be EHN. It follows from the requirement that
the PROPOSED replacement map itself be EHN. -/
theorem oneVertexRecolor_occupiedWithinCoveredSet_notEHN
    {V UT : Type} [DecidableEq V]
    (Source : Structure L V) (Target : Structure L UT)
    (f : V → UT)
    (S : Set V) (hCover : PairwiseIrreducibleSourceTestCover Source S)
    (a b : V) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (d : UT) (hOccupied : f b = d) :
    ¬ Source.IsEHNHomomorphismEmbedding Target
      (fun z : V => if z = a then d else f z) := by
  intro hNewEHN
  have hSame :
      (fun z : V => if z = a then d else f z) a =
      (fun z : V => if z = a then d else f z) b := by
    simp [hab.symm, hOccupied]
  have hInj := ehn_injOn_of_pairwiseIrreducibleSourceTestCover
    Source Target
    (fun z : V => if z = a then d else f z)
    hNewEHN S hCover
  exact hab (hInj ha hb hSame)

end AllThoseRamseyClasses.Lifts
