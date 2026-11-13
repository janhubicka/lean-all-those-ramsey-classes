import AllThoseRamseyClasses.Published.TrackEOriginalNativeInducedUIrreducible
import PartiteConstruction.Functional.TrackEFinalCoveredDecodedClosedU2019
import PartiteConstruction.Functional.WeakInvariant

/-!
# Track C: a native EHN map already protects exact irreducible OLD images

The second native internal-B-cover pass produces a weak EHN projection
q : D → P, where P is the ORIGINAL decoded functional target of the
actual final tagged 2019 sparse witness C. An arbitrary EHN map is NOT
a globally protected OLD/U map, and the paper must never infer this.

However, for every genuinely irreducible FULL native source test
e : E ↪ D, the EHN condition gives a FULL embedding of the very
same E into P on q ∘ e. The merged Track E actual-source geometric
lemma then proves that the EXACT range of this particular native
embedding is both U-closed and U-irreducible in the ACTUAL tagged C.

No closure hull of the image, no global full q, no canonical re-tagging
of C, and no root/vertex rank condition are used. This is the
source-test protection stage of the English cover-and-pullback route.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type w} [Fintype Parts]
variable {V W X : Type v}

/-- A genuinely irreducible full test of an arbitrary native EHN source
has a SAME-MAP full image in the actual decoded functional target P
whose literal vertex set is U-closed and U-irreducible in C.

The exact image may be much larger than one input-root seed but it
is never replaced by an ambient U-closure hull. -/
theorem genuineTagged2019_EHN_irredTest_has_exact_protectedImage
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (Base : PartialSetStructure L W) (basePart : W → Parts)
    (hC : IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hPos : L.PositiveFuncArity)
    (hCover : ∀ {Y : Type v}
      (Test : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) Y),
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts) Test →
      Embedding Test C →
      Nonempty (Embedding Test
        (wholeMaskTagExpansion
          ((Base.withParts basePart).wholeMaskPatternGraph basePart))))
    (D : Structure L X) (q : X → V)
    (hq : D.IsEHNHomomorphismEmbedding
      ((wholeMaskOriginalDecode C).collapseDomain) q)
    {T : Type v} (E : Structure L T)
    (hE : E.Irreducible) (e : Structure.Embedding E D) :
    ∃ g : Structure.Embedding E
        ((wholeMaskOriginalDecode C).collapseDomain),
      (∀ x : T, g x = q (e x)) ∧
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (Set.range g)) ∧
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce (Set.range g)) := by
  classical
  obtain ⟨g, hg⟩ := hq.2 E hE e
  let S : Set V := Set.range g
  have hNativeClosed :
      ((wholeMaskOriginalDecode C).collapseDomain).IsClosed S :=
    g.range_isClosed
  have hOriginalClosed : (wholeMaskOriginalDecode C).IsClosed S :=
    ((wholeMaskOriginalDecode C).isClosed_iff_collapseDomain_isClosed S).mpr
      hNativeClosed
  let Plus : PartialSetStructure (L.withParts Parts) V :=
    (wholeMaskTagReduct C).wholeMaskPartialDecode
  have hPlusClosed : Plus.IsClosed S := by
    intro F xs U hxs hVal
    exact hOriginalClosed F.down xs U hxs hVal
  have hExactClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce S) :=
    wholeMaskCovered_decodedClosed_to_inducedUClosed
      C (Base.withParts basePart) basePart
      hC (hPos.withParts) hCover S hPlusClosed
  have hExactIrred :
      IsUIrreducible ((L.withParts Parts).wholeMaskClosureRules Parts)
        (C.induce S) :=
    wholeMaskCovered_originalNativeIrredCopy_UIrreducible
      C Base basePart hC hPos hCover E hE g
  exact ⟨g, hg, hExactClosed, hExactIrred⟩

end AllThoseRamseyClasses.Published
