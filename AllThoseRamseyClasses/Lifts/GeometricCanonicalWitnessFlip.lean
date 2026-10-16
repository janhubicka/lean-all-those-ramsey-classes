import AllThoseRamseyClasses.Lifts.FixedRootCanonicalWitness
import AllThoseRamseyClasses.Lifts.GeometricCanonicalFlip

/-!
# Extract a geometric forbidden-source flip from a canonical lift witness

Let d be a genuine minimal function-closed separating cut in a
forbidden source A. Its ordered tuple bijectively enumerates the
full induced root on R = range d.roots.

If the canonical extra relation for the original piece class holds
on a corresponding tuple of a second ambient structure B, its exact
semantics supplies an EQUIVALENT replacement root extension Q and
a weak/EHN map into B matching all ordered root coordinates.

A full embedding B -> Target and surjectivity of the enumeration
promote the coordinate equations into an equality of weak maps on
EVERY vertex of the induced root. Thus the already verified geometric
canonical flip constructs a new literal forbidden source and a weak
map to Target unchanged on the whole complementary side.

The extra relation explicitly requires injective root images. A
weak HE alone need not ensure them; we prove the root-injectivity
consequence separately and do not silently assume it.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V UB UT : Type v}

/-- The ordered separator tuple enumerates EXACTLY its vertex-set
subtype, with no generated-closure vertices added to the root. -/
noncomputable def geometricCutRootEquiv
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) :
    Fin n ≃ Set.range d.roots := by
  let f : Fin n → Set.range d.roots :=
    fun i => ⟨d.roots i, ⟨i, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j h
    apply d.roots_injective
    exact congrArg Subtype.val h
  · intro r
    rcases r.2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi

@[simp] theorem geometricCutRootEquiv_val
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n) (i : Fin n) :
    (geometricCutRootEquiv A d i).1 = d.roots i := rfl

/-- A canonical relation in B, whose tuple is carried by an
embedding B -> Target to the root image of a source map f,
forces the root image of f to be injective. -/
theorem canonicalGeometricRootImage_injective
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (B : Structure L UB) (Target : Structure L UT)
    (jB : Structure.Embedding B Target)
    (f : V → UT) (xsB : Fin n → UB)
    (hCoordinates : ∀ i : Fin n,
      jB (xsB i) = f (d.roots i))
    (hCanonical :
      (enumeratedRootClassCanonicalLift
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        (geometricCutRootEquiv A d)
        F
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left)
        B).rel (.inr PUnit.unit) xsB) :
    Function.Injective (fun i : Fin n => f (d.roots i)) := by
  have hrel := (enumeratedRootClassCanonicalRelation_iff
      (closedCutRoot A (Set.range d.roots) d.minimal.1)
      (geometricCutRootEquiv A d) F
      (componentPieceRootExtension A (Set.range d.roots)
        d.minimal.1 d.left) B xsB).mp hCanonical
  have hinj : Function.Injective xsB := hrel.1
  intro i j hij
  apply hinj
  apply jB.injective
  calc
    jB (xsB i) = f (d.roots i) := hCoordinates i
    _ = f (d.roots j) := hij
    _ = jB (xsB j) := (hCoordinates j).symm

/-- The exact piece and weak map supplied by a canonical relation in
the second witness generate a flip of the original geometric
minimal-cut forbidden source.

Besides the replacement source, the output includes the replacement
piece Q and the weak realizing map g into B. This avoids using
arbitrary choice to hide the proof of witness extraction. -/
theorem geometricMinimalPieceFlip_of_canonicalRelation
    (A : Structure L V) {n : ℕ}
    (d : GeometricFunctionalPieceData A n)
    (F : ∀ {W : Type v}, Structure L W → Prop)
    (hFA : F A)
    (Target : Structure L UT)
    (f : V → UT)
    (hf : A.IsEHNHomomorphismEmbedding Target f)
    (B : Structure L UB)
    (jB : Structure.Embedding B Target)
    (xsB : Fin n → UB)
    (hCoordinates : ∀ i : Fin n,
      jB (xsB i) = f (d.roots i))
    (hCanonical :
      (enumeratedRootClassCanonicalLift
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        (geometricCutRootEquiv A d)
        F
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left)
        B).rel (.inr PUnit.unit) xsB) :
    ∃ Q : FunctionalRootExtension
        (closedCutRoot A (Set.range d.roots) d.minimal.1),
      (functionalRootPieceSetoid
        (closedCutRoot A (Set.range d.roots) d.minimal.1)
        F).r
        (componentPieceRootExtension A (Set.range d.roots)
          d.minimal.1 d.left) Q ∧
      ∃ (g : Q.Carrier → UB),
        Q.str.IsEHNHomomorphismEmbedding B g ∧
        (∀ i : Fin n,
          g (Q.rootEmbedding (geometricCutRootEquiv A d i)) = xsB i) ∧
        ∃ (W : Type v) (Source : Structure L W),
          F Source ∧
          ∃ (iP : Structure.Embedding Q.str Source)
            (iC : Structure.Embedding
              (componentComplementRootExtension A
                (Set.range d.roots) d.minimal.1 d.left).str Source),
            Structure.IsFreeAmalgam Q.rootEmbedding
              (componentComplementRootExtension A
                (Set.range d.roots) d.minimal.1 d.left).rootEmbedding
              iP iC ∧
            ∃ flip : W → UT,
              Source.IsEHNHomomorphismEmbedding Target flip ∧
              (∀ a : Q.Carrier,
                flip (iP a) = jB (g a)) ∧
              ∀ b : (componentComplementRootExtension A
                  (Set.range d.roots) d.minimal.1 d.left).Carrier,
                flip (iC b) = f b.1 := by
  obtain ⟨_hinj, Q, hEq, g, hg, hroot⟩ :=
    (enumeratedRootClassCanonicalRelation_iff
      (closedCutRoot A (Set.range d.roots) d.minimal.1)
      (geometricCutRootEquiv A d)
      F
      (componentPieceRootExtension A (Set.range d.roots)
        d.minimal.1 d.left)
      B xsB).mp hCanonical
  have hTarget :
      Q.str.IsEHNHomomorphismEmbedding Target (jB ∘ g) :=
    jB.isEHNHomomorphismEmbedding.comp hg
  have hEntireRoot :
      ∀ r : Set.range d.roots,
        (jB ∘ g) (Q.rootEmbedding r) = f r.1 := by
    intro r
    obtain ⟨i, hi⟩ := (geometricCutRootEquiv A d).surjective r
    subst r
    calc
      (jB ∘ g) (Q.rootEmbedding (geometricCutRootEquiv A d i)) =
          jB (xsB i) := congrArg jB (hroot i)
      _ = f (d.roots i) := hCoordinates i
      _ = f (geometricCutRootEquiv A d i).1 := by rfl
  obtain ⟨W, Source, hF, iP, iC, hfree, flip, hflip, hp, hc⟩ :=
    geometricMinimalPieceCanonicalFlip A d F hFA
      Target f hf Q hEq (jB ∘ g) hTarget hEntireRoot
  exact ⟨Q, hEq, g, hg, hroot,
    W, Source, hF, iP, iC, hfree, flip, hflip, hp, hc⟩

end AllThoseRamseyClasses.Lifts
