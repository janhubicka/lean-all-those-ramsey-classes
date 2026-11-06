import AllThoseRamseyClasses.Published.FunctionalWithParts2019CorrectedWeakCanonical
import PartiteConstruction.Functional.WholeMaskCoveredTargetDomains2019

/-!
# Track C: actual corrected (4b) implies two complete-mask OLD laws

A candidate satisfying closed U-irreducible K-membership need not be
a canonical genuinely partial structure globally. Nevertheless every
ordinary irreducible exact weak test has SOME full canonical H-target,
with no fixed B. That suffices to reflect two OLD local laws:

* a complete output tuple has an injective distinct-input root
  and its corresponding active domain-mask tuple;
* any two active domain masks with the identical input pattern/root
  describe the same SET of output parts.

Both are consequences of the original corrected clause (4b), not
extra assumptions. The target H-member may vary with each weak test.

These laws do not yet yield a coherent unique COMPLETE output vertex
set across separate witnesses for one primitive application; proving
that requires placing both entire tuples into one canonical
U-irreducible hull, using their common input roots and tag normality.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.PartialSetStructure

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Exact corrected (4b) supplies the original OLD law that every
complete output tuple activates its matching input-domain mask,
including a zero-width defined-empty output mask. -/
theorem genuineTagged2019_correctedCovered_validCompleteMaskDomains
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C) :
    HasValidCompleteMaskDomains (wholeMaskTagReduct C) := by
  classical
  intro p q t ht
  let S : Set V := Set.range t
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inr (p,q)))) t ht
  obtain ⟨X, hX, Target, partTarget, _, _, ⟨g⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hX
  let T := Target.withParts partTarget
  let ts : Fin (p.rootSize + q.size) → S :=
    fun j => ⟨t j, ⟨j, rfl⟩⟩
  have hBT : (T.wholeMaskPatternGraph partTarget).rel
      (.inr (.inr (p,q))) (g ∘ ts) :=
    (g.map_rel_iff (.inl (.inr (.inr (p,q)))) ts).mpr ht
  obtain ⟨hInjectiveB, hDomainB⟩ :=
    StructuralRamsey.RelStructure.PartialSetStructure.wholeMaskPatternGraph_validDomains
      T partTarget p q (g ∘ ts) hBT
  let rS : Fin p.rootSize → S :=
    fun i => ts (Fin.castAdd q.size i)
  have hInjective :
      Function.Injective
        (fun i : Fin p.rootSize => t (Fin.castAdd q.size i)) := by
    intro i j hij
    apply hInjectiveB
    change g (rS i) = g (rS j)
    exact congrArg g (Subtype.ext hij)
  have hLocal : (C.induce S).rel
      (.inl (.inr (.inl (p,q)))) rS :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q)))) rS).mp hDomainB
  have hAmbient : C.rel
      (.inl (.inr (.inl (p,q))))
      (fun i => t (Fin.castAdd q.size i)) := hLocal
  exact ⟨hInjective, hAmbient⟩

/-- The corrected closed-test class membership also forces the SAME
output-part SET at every OLD active domain with a common input
equality pattern and root. Enumeration orders may still differ. -/
theorem genuineTagged2019_correctedCovered_uniqueDomainSets
    (H : GenuinePartite2019Class (L := L) (Parts := Parts))
    (C : RelStructure ((L.withParts Parts).wholeMaskTagLanguage Parts) V)
    (hClosed :
      IsUClosed ((L.withParts Parts).wholeMaskClosureRules Parts) C)
    (hCovered :
      CorrectedUIrreduciblesIn
        (canonicalGenuineTagged2019Class H)
        ((L.withParts Parts).wholeMaskClosureRules Parts) C) :
    HasUniqueWholeMaskDomainSets (wholeMaskTagReduct C) := by
  classical
  intro p q₁ q₂ root h₁ h₂
  let S : Set V := Set.range root
  have hIrred : (C.induce S).Irreducible :=
    relationTuple_range_irreducible C
      (.inl (.inr (.inl (p,q₁)))) root h₁
  obtain ⟨X, hX, Target, partTarget, _, _, ⟨g⟩⟩ :=
    genuineTagged2019_correctedCovered_weakIrred_canonicalTarget
      H C hClosed hCovered S hIrred
  letI : Finite X := hX
  let T := Target.withParts partTarget
  let rS : Fin p.rootSize → S :=
    fun i => ⟨root i, ⟨i, rfl⟩⟩
  have hS₁ : (C.induce S).rel
      (.inl (.inr (.inl (p,q₁)))) rS := h₁
  have hS₂ : (C.induce S).rel
      (.inl (.inr (.inl (p,q₂)))) rS := h₂
  have hB₁ : (T.wholeMaskPatternGraph partTarget).rel
      (.inr (.inl (p,q₁))) (g ∘ rS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q₁)))) rS).mpr hS₁
  have hB₂ : (T.wholeMaskPatternGraph partTarget).rel
      (.inr (.inl (p,q₂))) (g ∘ rS) :=
    (g.map_rel_iff (.inl (.inr (.inl (p,q₂)))) rS).mpr hS₂
  exact T.wholeMaskPatternGraph_domain_mask_set_unique
    partTarget p q₁ q₂ (g ∘ rS) hB₁ hB₂

end AllThoseRamseyClasses.Published
