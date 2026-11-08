import AllThoseRamseyClasses.Lifts.GlobalCountableFraisseExtensionDiagrams
import AllThoseRamseyClasses.Lifts.GlobalSurjectiveFullEmbeddingInverse

/-!
# Track F: every finite FULL age extension has an actual representative diagram

A fair Fraisse schedule enumerates all FULL embeddings P ↪ Q
between labelled finite original maximal-trace age representatives
on Fin n and Fin m. The eventual full extension-property theorem
must also handle an arbitrary FULL extension i : A ↪ B between
unlabelled finite age members.

This module builds, from such an i, an ACTUAL representative
diagram d : P ↪ Q plus genuine surjective FULL embeddings
a : P ↪ A and b : Q ↪ B whose square commutes:

                   d
              P ----------> Q
              |             |
            a |             | b
              v             v
              A ----------> B
                   i

The right representative-to-B map b is inverted by the
verified full surjective embedding inverse (#931). This
retains the exact whole set-valued function fibres and all
old/new relations, rather than merely a weak EHN map.

The result makes no claim about the existence or age of
the infinite direct limit. It is valid under the genuine
conditional finite-age Fraisse input and does not disguise
the unrestricted original shadow-avoidance gap.
The numbered 2019 ramsey.tex remains frozen.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- EVERY actual finite full age extension A ↪ B is the
full-isomorphic transport of one actual labelled finite
representative diagram d:P ↪ Q.

Only B's finite age membership is required: full heredity
supplies membership of A. The two vertical maps are SURJECTIVE
FULL functional embeddings, and the square commutes on every
root vertex. Thus all relation truth values and complete
partial-function fibres are transported without loss. -/
theorem globalOriginalFiniteTraceDiagram_represents_fullExtension
    (F : ∀ {W : Type}, Structure L W → Prop)
    (hInput : GlobalOriginalFiniteFraisseInput F)
    {VA VB : Type}
    (A : Structure (globalFunctionalPieceLanguage F) VA)
    (B : Structure (globalFunctionalPieceLanguage F) VB)
    (hB : IsGlobalFiniteMaximalTrace F
      (fun {W : Type} (C : Structure L W) =>
        AvoidsGlobalFunctionalEHN F C) B)
    (i : Structure.Embedding A B) :
    ∃ (d : GlobalOriginalFiniteTraceDiagram F),
      ∃ (a : Structure.Embedding d.1.2.1 A)
        (b : Structure.Embedding d.2.1.2.1 B),
        Function.Surjective a ∧ Function.Surjective b ∧
        ∀ x, b (d.2.2 x) = i (a x) := by
  have hA := hInput.finiteAgeCore.hereditary i hB
  obtain ⟨P, a, ha⟩ :=
    hInput.coversEveryAgeMember A hA
  obtain ⟨Q, b, hb⟩ :=
    hInput.coversEveryAgeMember B hB
  let bInv : Structure.Embedding B Q.2.1 :=
    fullEmbeddingInverseOfSurjective b hb
  let dPQ : Structure.Embedding P.2.1 Q.2.1 :=
    bInv.comp (i.comp a)
  refine ⟨⟨P, Q, dPQ⟩, a, b, ha, hb, ?_⟩
  intro x
  change b (bInv (i (a x))) = i (a x)
  exact fullEmbeddingInverseOfSurjective_rightInverse
    b hb (i (a x))

end AllThoseRamseyClasses.Lifts
