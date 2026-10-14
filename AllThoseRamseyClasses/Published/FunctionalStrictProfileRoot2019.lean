import AllThoseRamseyClasses.Published.GeneratedClosureProfileBoundary2019

/-!
# A common closed root inside BOTH Base copies (strict functional target)

A strict tree of canonical generated-closure profiles supplies a full
profile embedding of its weak gluing root into an actual Base copy on
each side.  The common profile determines ONE actual closed hull inside
Base, with full embeddings into BOTH of those actual copies; no
completion map and no choice of arbitrary ambient root is involved.

Composing with embeddings of the two Base copies into larger U-closed
tree sides gives the exact common closed root needed by a strict
full-function free-amalgam gluing step.

This is the verified root constructor, *not* by itself a proof that
every profiled tree admits a strict functional completion.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- Two actual canonical profile-Base copies sharing the same induced
weak profile root have a compatible full common U-closed Base hull,
which embeds into any two targets containing these Base copies.

The witnesses agree on every original root vertex.  Their images are
each contained in a single actual Base copy, a stronger property than
mere containment in some arbitrary completion target. -/
theorem closureProfile2019_two_base_copies_closed_root
    {K : StructureClass.{u,v} (L := L)}
    {rules : ClosureDescription L}
    {UB H X Y : Type v} [Fintype H]
    (Base : RelStructure L UB)
    (Left : RelStructure L X) (Right : RelStructure L Y)
    (hBase : IsUClosed rules Base) (hBaseK : K Base)
    (hHer : ClosedUHereditary K rules)
    (Root : RelStructure (closureProfileLanguage2019 rules Base) H)
    (rL : Embedding Root (closureProfileExpansion2019 rules Base Base))
    (rR : Embedding Root (closureProfileExpansion2019 rules Base Base))
    (bL : Embedding Base Left) (bR : Embedding Base Right) :
    ∃ (S : Set UB)
      (aL : Embedding (Base.induce S) Left)
      (aR : Embedding (Base.induce S) Right)
      (q : H → S),
      IsUClosed rules (Base.induce S) ∧
      K (Base.induce S) ∧
      (∀ h, aL (q h) = bL (rL h)) ∧
      (∀ h, aR (q h) = bR (rR h)) := by
  obtain ⟨S, xL, xR, q, hSClosed, hSK, hQL, hQR⟩ :=
    closureProfile2019_common_weak_root_closed_boundary
      Base Base hBase hBaseK hHer Root rL rR
  refine ⟨S, bL.comp xL, bR.comp xR, q,
    hSClosed, hSK, ?_, ?_⟩
  · intro h
    exact congrArg bL (hQL h)
  · intro h
    exact congrArg bR (hQR h)

end AllThoseRamseyClasses.Published
