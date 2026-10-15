import AllThoseRamseyClasses.Lifts.ComponentPieces
import PartiteConstruction.Iterated.FreeAmalgam

/-!
# Free gluing of rooted relational structures

The next ingredient of `sec:regular`, immediately before manuscript
Definition `def:incompatible`. Two rooted structures of the same width
can be glued only when their *entire induced root structures agree*,
including reflection of negative relational tuples. Distinct widths,
or merely two injective root tuples, do not suffice.

The concrete free amalgam is reused from the already formalized
partite-construction library. At this stage the source language is
relational, and rooted carriers are in `Type` (universe 0), matching
the uniform-carrier-universe API of the current free-amalgam module.
The paper's partial functions and arbitrary universe levels require
the appropriate separate embedding interface, not coercions.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u
variable {L : RelLanguage.{u}} {n : ℕ}

/-- Exactly the induced structure on the ORDERED root tuple of P.
Repeated tuple positions, negative relations, and zero-ary symbols
are all reflected in this reduct. -/
def rootReduct (P : RootedPattern.{u,0} L n) :
    RelStructure L (Fin n) where
  rel s xs := P.str.rel s (P.root ∘ xs)

/-- The ordered root tuple is a genuine full embedding of its
induced root structure, not just a relational homomorphism. -/
def rootEmbedding (P : RootedPattern.{u,0} L n) :
    Embedding (rootReduct P) P.str where
  toFun := P.root
  injective := P.root_injective
  map_rel_iff s xs := Iff.rfl

/-- The paper's compatibility condition for defining P ⊕ Q:
induced root structures are isomorphic via the specified root order. -/
def RootCompatible (P Q : RootedPattern.{u,0} L n) : Prop :=
  rootReduct P = rootReduct Q

theorem rootCompatible_refl (P : RootedPattern.{u,0} L n) :
    RootCompatible P P := rfl

theorem rootCompatible_symm {P Q : RootedPattern.{u,0} L n}
    (h : RootCompatible P Q) : RootCompatible Q P := h.symm

theorem rootCompatible_trans {P Q T : RootedPattern.{u,0} L n}
    (hPQ : RootCompatible P Q) (hQT : RootCompatible Q T) :
    RootCompatible P T := hPQ.trans hQT

/-- A compatible right-hand root can be viewed as an embedding of
the LEFT root reduct into Q. The compatibility proof gives full
reflection of the entire induced root structure. -/
def compatibleRightRootEmbedding
    (P Q : RootedPattern.{u,0} L n)
    (h : RootCompatible P Q) :
    Embedding (rootReduct P) Q.str where
  toFun := Q.root
  injective := Q.root_injective
  map_rel_iff s xs := by
    change (rootReduct Q).rel s xs ↔ (rootReduct P).rel s xs
    rw [h]

/-- Concrete rooted free gluing of P and Q over the entire common
root structure. This is the actual free amalgamation construction;
it assumes NO membership in a forbidden class. -/
noncomputable def rootedFreeAmalgam
    (P Q : RootedPattern.{u,0} L n)
    (h : RootCompatible P Q) :=
  FreeAmalgam.amalgam (rootReduct P) P.str Q.str
    (rootEmbedding P) (compatibleRightRootEmbedding P Q h)

/-- The canonical embedding of the left rooted structure. -/
noncomputable def rootedFreeAmalgamLeft
    (P Q : RootedPattern.{u,0} L n) (h : RootCompatible P Q) :
    Embedding P.str (rootedFreeAmalgam P Q h) :=
  FreeAmalgam.leftEmbedding (rootReduct P) P.str Q.str
    (rootEmbedding P) (compatibleRightRootEmbedding P Q h)

/-- The canonical embedding of the right rooted structure. -/
noncomputable def rootedFreeAmalgamRight
    (P Q : RootedPattern.{u,0} L n) (h : RootCompatible P Q) :
    Embedding Q.str (rootedFreeAmalgam P Q h) :=
  FreeAmalgam.rightEmbedding (rootReduct P) P.str Q.str
    (rootEmbedding P) (compatibleRightRootEmbedding P Q h)

/-- The left and right injections agree exactly on all corresponding
root vertices: no identification away from the common root. -/
theorem rootedFreeAmalgam_roots_agree
    (P Q : RootedPattern.{u,0} L n) (h : RootCompatible P Q)
    (i : Fin n) :
    rootedFreeAmalgamLeft P Q h (P.root i) =
      rootedFreeAmalgamRight P Q h (Q.root i) := by
  exact FreeAmalgam.left_right_overlap (rootReduct P) P.str Q.str
    (rootEmbedding P) (compatibleRightRootEmbedding P Q h) i

/-- The glued structure satisfies the genuine strong, relational free
amalgamation certificate of the shared library. -/
theorem rootedFreeAmalgam_isFreeAmalgam
    (P Q : RootedPattern.{u,0} L n) (h : RootCompatible P Q) :
    IsFreeAmalgam (rootEmbedding P) (compatibleRightRootEmbedding P Q h)
      (rootedFreeAmalgamLeft P Q h)
      (rootedFreeAmalgamRight P Q h) :=
  FreeAmalgam.isFreeAmalgam (rootReduct P) P.str Q.str
    (rootEmbedding P) (compatibleRightRootEmbedding P Q h)

/-- Explicit relational isomorphism, not merely homomorphisms or
embeddings both ways. This is the equivalence used to recognize a
forbidden glued pattern up to a change of vertex names. -/
def RelIsomorphic {U V : Type} (A : RelStructure L U)
    (B : RelStructure L V) : Prop :=
  ∃ f : U ≃ V, ∀ s xs, B.rel s (f ∘ xs) ↔ A.rel s xs

/-- Being isomorphic to a member of a forbidden family. The source
family need not have isomorphism closure as a primitive class axiom. -/
def ForbiddenUpToIso
    (F : StructureClass.{u,0} (L := L))
    {U : Type} (A : RelStructure L U) : Prop :=
  ∃ (V : Type) (B : RelStructure L V), F B ∧ RelIsomorphic A B

/-- The manuscript's rooted incompatibility test, now given by an
ACTUAL free amalgam, when both arguments are rooted patterns of the
same width. Incompatibility is only defined when the roots agree.

This formula becomes Definition `def:incompatible` once the first
argument is restricted to actual geometric pieces of forbidden
connected structures and the second is allowed to range over every
rooted structure. -/
def IncompatibleByFreeGluing
    (F : StructureClass.{u,0} (L := L))
    (P Q : RootedPattern.{u,0} L n) : Prop :=
  ∃ h : RootCompatible P Q,
    ForbiddenUpToIso F (rootedFreeAmalgam P Q h)

end AllThoseRamseyClasses.Lifts
