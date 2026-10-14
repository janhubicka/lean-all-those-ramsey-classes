import PartiteConstruction.Ramsey.ClosureFreeAmalgamCompletion
import PartiteConstruction.Iterated.LocalTreeLike

/-!
# Strict amalgam trees with genuinely closed functional roots

The ordinary relational strict TreeAmalgam allows roots contained in
irreducibles but need not close those roots under a closure description.

A strict tree of genuine partial-function structures needs BOTH:
the original irreducible-container condition and U-closedness of
each gluing root.  Those conditions are recorded at EVERY step,
not inferred incorrectly from the final target being U-closed.

The resulting tree is a strict relational tree; every node of the
construction is U-closed. This is the source-faithful target notion
for converting the tree back to full partial-function embeddings.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}}

/-- A strict relational B-tree whose copies and gluing roots are
genuinely closed under the same closure description. -/
inductive UClosedStrictTreeAmalgam
    (rules : ClosureDescription L) {VB : Type v}
    (Base : RelStructure L VB) :
    (W : Type v) → RelStructure L W → Prop
  | copy {W : Type v} {T : RelStructure L W}
      (hIso : Iso Base T) (hT : IsUClosed rules T) :
      UClosedStrictTreeAmalgam rules Base W T
  | glue
      {W₁ W₂ H W : Type v}
      {T₁ : RelStructure L W₁} {T₂ : RelStructure L W₂}
      {Root : RelStructure L H} {T : RelStructure L W}
      (h₁ : UClosedStrictTreeAmalgam rules Base W₁ T₁)
      (h₂ : UClosedStrictTreeAmalgam rules Base W₂ T₂)
      (hRoot : IsUClosed rules Root)
      (f₁ : Embedding Root T₁) (f₂ : Embedding Root T₂)
      (hc₁ : f₁.ContainedInIrreducible)
      (hc₂ : f₂.ContainedInIrreducible)
      (i₁ : Embedding T₁ T) (i₂ : Embedding T₂ T)
      (hfree : IsFreeAmalgam f₁ f₂ i₁ i₂) :
      UClosedStrictTreeAmalgam rules Base W T

namespace UClosedStrictTreeAmalgam

/-- Forget the closed-root certificates, preserving strictness. -/
theorem toTreeAmalgam
    {rules : ClosureDescription L} {VB W : Type v}
    {Base : RelStructure L VB} {T : RelStructure L W}
    (h : UClosedStrictTreeAmalgam rules Base W T) :
    TreeAmalgam Base W T := by
  induction h with
  | copy hIso hT =>
      exact TreeAmalgam.copy hIso
  | @glue W₁ W₂ H W T₁ T₂ Root T
      h₁ h₂ hRoot f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact TreeAmalgam.glue ih₁ ih₂ f₁ f₂ hc₁ hc₂ i₁ i₂ hfree

/-- Closedness holds at every node of a closed-root strict tree. -/
theorem isUClosed
    {rules : ClosureDescription L} {VB W : Type v}
    {Base : RelStructure L VB} {T : RelStructure L W}
    (h : UClosedStrictTreeAmalgam rules Base W T) :
    IsUClosed rules T := by
  induction h with
  | copy hIso hT =>
      exact hT
  | @glue W₁ W₂ H W T₁ T₂ Root T
      h₁ h₂ hRoot f₁ f₂ hc₁ hc₂ i₁ i₂ hfree ih₁ ih₂ =>
      exact hfree.isUClosed hRoot ih₁ ih₂

end UClosedStrictTreeAmalgam
end AllThoseRamseyClasses.Published
