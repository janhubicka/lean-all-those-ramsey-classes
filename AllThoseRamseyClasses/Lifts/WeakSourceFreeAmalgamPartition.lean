import PartiteConstruction.Structure.FreeAmalgam
import PartiteConstruction.Structure.GeneratedWeakHomImage

/-!
# Pulling back the three vertex regions of a functional free amalgam

The proof of the Section 3 strong-amalgamation lemma partitions the
vertices of a forbidden source mapped into a FULL free amalgam
D = Left ⊕_Root Right into three regions:
- vertices mapped into the shared root,
- vertices mapped into the exclusive left side,
- vertices mapped into the exclusive right side.

This does NOT require the forbidden source map to be injective.
The shared root is function-closed in D since it is the range of a
full functional embedding, and its PREIMAGE is closed under
every weak functional homomorphism. The three regions cover the
entire source and are pairwise disjoint by exact free-amalgam overlap.

These are the rigorous first steps before considering Gaifman
components and minimizing one side. They avoid the currently
unproved general reduction of a weak forbidden map to an injective
one by tuple-surjective images.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- Preimage of the EXACT common root in Whole, using the full
root inclusion on the left. Its image on the right agrees by the
free-amalgam overlap certificate. -/
def weakFreeRootPart
    (f : U → W) : Set U :=
  {x | f x ∈ Set.range (iL.comp sL)}

/-- The vertices whose images belong to the left side but not
to the shared root. -/
def weakFreeLeftPart
    (f : U → W) : Set U :=
  {x | (∃ a : E, f x = iL a) ∧
    x ∉ (weakFreeRootPart (sL := sL) (iL := iL) f)}

/-- The vertices whose images belong to the right side but not
to the shared root. -/
def weakFreeRightPart
    (f : U → W) : Set U :=
  {x | (∃ b : F, f x = iR b) ∧
    x ∉ (weakFreeRootPart (sL := sL) (iL := iL) f)}

/-- A weak functional map pulls the common full root back to a
FUNCTION-CLOSED source set; no injectivity of f is assumed. -/
theorem weakFreeRootPart_isClosed
    (f : U → W)
    (hf : Source.IsWeakHomomorphism Whole f) :
    Source.IsClosed (weakFreeRootPart (sL := sL) (iL := iL) f) := by
  exact hf.preimage_isClosed (Set.range (iL.comp sL))
    (iL.comp sL).range_isClosed

/-- The three regions cover every vertex of a source mapping
weakly into the whole functional free amalgam. -/
theorem weakFreePartition_covers
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (x : U) :
    x ∈ weakFreeRootPart (sL := sL) (iL := iL) f ∨
      x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f ∨
        x ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f := by
  by_cases hroot :
      x ∈ weakFreeRootPart (sL := sL) (iL := iL) f
  · exact Or.inl hroot
  · rcases hfree.covers (f x) with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inr (Or.inl ⟨⟨a, ha⟩, hroot⟩)
    · exact Or.inr (Or.inr ⟨⟨b, hb⟩, hroot⟩)

/-- The two exclusive regions are disjoint by the exact
root-overlap condition of the full free amalgam. -/
theorem weakFreePartition_left_right_disjoint
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) :
    Disjoint
      (weakFreeLeftPart (sL := sL) (iL := iL) f)
      (weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f) := by
  apply Set.disjoint_left.mpr
  intro x hxLeft hxRight
  obtain ⟨⟨a, ha⟩, hnotRoot⟩ := hxLeft
  obtain ⟨⟨b, hb⟩, _⟩ := hxRight
  have hab : iL a = iR b := ha.symm.trans hb
  obtain ⟨r, hrL, _hrR⟩ := (hfree.overlap a b).mp hab
  apply hnotRoot
  refine ⟨r, ?_⟩
  change iL (sL r) = f x
  calc
    iL (sL r) = iL a := congrArg iL hrL.symm
    _ = f x := ha.symm

/-- The root region is automatically disjoint from either
exclusive side by its literal definition. -/
theorem weakFreePartition_root_exclusive
    (f : U → W) :
    Disjoint
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      (weakFreeLeftPart (sL := sL) (iL := iL) f) ∧
    Disjoint
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      (weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f) := by
  constructor
  · apply Set.disjoint_left.mpr
    intro x hroot hleft
    exact hleft.2 hroot
  · apply Set.disjoint_left.mpr
    intro x hroot hright
    exact hright.2 hroot

/-- The exact partition of Source used to start the
minimal-support argument of the homogenisation proof. -/
theorem weakFreePartition_univ
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) :
    Set.univ =
      weakFreeRootPart (sL := sL) (iL := iL) f ∪
        weakFreeLeftPart (sL := sL) (iL := iL) f ∪
          weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f := by
  ext x
  constructor
  · intro _
    rcases weakFreePartition_covers hfree f x with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro _
    trivial

end AllThoseRamseyClasses.Lifts
