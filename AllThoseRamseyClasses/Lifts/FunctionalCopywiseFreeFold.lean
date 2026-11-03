import PartiteConstruction.Structure.FreeAmalgam
import PartiteConstruction.Functional.RankedTreeReduct

/-!
# Track E: full functional copywise completion across free source amalgams

A source free amalgam in a genuine functional language carries no
relation or set-valued function incidence crossing its two sides.
A target strong amalgam of already completed sides need NOT be free
in its relation/function signature.

If two vertex maps out of the source sides agree after embedding
their completed targets over the full common root, they can be
folded to one vertex map on the whole source. The fold is not
required to be globally injective, a homomorphism, or an embedding.
Nevertheless, if the designated Base is FULL-function irreducible,
every Base-copy in the source is on one side, and its restriction
is a FULL functional embedding in the target.

This is the native functional analogue of the existing RELATIONAL
CopywiseFreeFold lemma in partite-construction. It does not
silently relationalize function graphs or assume function-closure
of an arbitrary weak vertex subset. Full embeddings reflect
complete original set-valued function fibres.

The generic lemma is independent of the finite forbidden family,
of maximal component tags, and of the missing sparse Ramsey
construction. The intended application is finite strong AP of the
hereditary maximal induced-trace age.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

variable {H E F C X Y Z P : Type}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L C}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- A fold of compatible vertex maps from a FULL functional
free-source amalgam. No target structural information is
required to define the fold, only agreement on the source root. -/
noncomputable def functionalCompatibleFold
    (hSrc : Structure.IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d : H, fL (sL d) = fR (sR d)) : C → X := by
  classical
  intro z
  exact if h : ∃ a : E, z = iL a then
      fL (Classical.choose h)
    else
      fR (Classical.choose ((hSrc.covers z).resolve_left h))

/-- A compatible fold agrees literally with the first side map. -/
theorem functionalCompatibleFold_left
    (hSrc : Structure.IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d : H, fL (sL d) = fR (sR d))
    (a : E) :
    functionalCompatibleFold hSrc fL fR hcompat (iL a) = fL a := by
  classical
  unfold functionalCompatibleFold
  have h : ∃ b : E, iL a = iL b := ⟨a, rfl⟩
  rw [dif_pos h]
  have heq : a = Classical.choose h :=
    iL.injective (Classical.choose_spec h)
  exact congrArg fL heq.symm

/-- A compatible fold also agrees with the second side map,
including at the common root, by the actual overlap law. -/
theorem functionalCompatibleFold_right
    (hSrc : Structure.IsFreeAmalgam sL sR iL iR)
    (fL : E → X) (fR : F → X)
    (hcompat : ∀ d : H, fL (sL d) = fR (sR d))
    (b : F) :
    functionalCompatibleFold hSrc fL fR hcompat (iR b) = fR b := by
  classical
  by_cases h : ∃ a : E, iR b = iL a
  · unfold functionalCompatibleFold
    rw [dif_pos h]
    have hroot : iL (Classical.choose h) = iR b :=
      (Classical.choose_spec h).symm
    obtain ⟨d, hdL, hdR⟩ :=
      (hSrc.overlap (Classical.choose h) b).mp hroot
    calc
      fL (Classical.choose h) = fL (sL d) :=
        congrArg fL hdL
      _ = fR (sR d) := hcompat d
      _ = fR b := congrArg fR hdR.symm
  · unfold functionalCompatibleFold
    rw [dif_neg h]
    let hb : ∃ c : F, iR b = iR c :=
      (hSrc.covers (iR b)).resolve_left h
    change fR (Classical.choose hb) = fR b
    have heq : Classical.choose hb = b :=
      iR.injective (Classical.choose_spec hb).symm
    exact congrArg fR heq

/-- Full functional copywise completion: one vertex map on the
source T restricts to a FULL embedding on every designated
Base-copy. No global homomorphism or injectivity of the map
is assumed. -/
def FunctionalCopywiseCompletion
    (Base : Structure L P)
    (Source : Structure L C)
    (Target : Structure L Z)
    (f : C → Z) : Prop :=
  ∀ e : Structure.Embedding Base Source,
    ∃ e' : Structure.Embedding Base Target,
      ∀ x : P, e' x = f (e x)

/-- Genuinely functional copywise completions of both sides can
be folded through a free SOURCE amalgam into an arbitrary
target containing FULL copies of both completed sides.

The target need not be a free amalgam. Every input/output fibre
on each copied Base is preserved exactly by the resulting
full target embedding; the arbitrary fold itself need not
preserve fibres on unrelated source tuples. -/
theorem FunctionalCopywiseCompletion.fold_free
    {Base : Structure L P}
    (hBase : Base.Irreducible)
    (hSrc : Structure.IsFreeAmalgam sL sR iL iR)
    {TL : Structure L X} {TR : Structure L Y}
    {Target : Structure L Z}
    (fL : E → X) (fR : F → Y)
    (hL : FunctionalCopywiseCompletion Base Left TL fL)
    (hR : FunctionalCopywiseCompletion Base Right TR fR)
    (jL : Structure.Embedding TL Target)
    (jR : Structure.Embedding TR Target)
    (hcompat : ∀ d : H,
      jL (fL (sL d)) = jR (fR (sR d))) :
    FunctionalCopywiseCompletion Base Whole Target
      (functionalCompatibleFold hSrc
        (jL ∘ fL) (jR ∘ fR) hcompat) := by
  classical
  intro e
  rcases hBase hSrc e with hleft | hright
  · let eL : Structure.Embedding Base Left :=
      e.factorThroughRange iL hleft
    obtain ⟨g, hg⟩ := hL eL
    refine ⟨jL.comp g, ?_⟩
    intro x
    calc
      (jL.comp g) x = jL (g x) := rfl
      _ = jL (fL (eL x)) := congrArg jL (hg x)
      _ = functionalCompatibleFold hSrc
            (jL ∘ fL) (jR ∘ fR) hcompat (iL (eL x)) :=
        (functionalCompatibleFold_left hSrc
          (jL ∘ fL) (jR ∘ fR) hcompat (eL x)).symm
      _ = functionalCompatibleFold hSrc
            (jL ∘ fL) (jR ∘ fR) hcompat (e x) := by
        exact congrArg
          (functionalCompatibleFold hSrc (jL ∘ fL) (jR ∘ fR) hcompat)
          (Classical.choose_spec (hleft x)).symm
  · let eR : Structure.Embedding Base Right :=
      e.factorThroughRange iR hright
    obtain ⟨g, hg⟩ := hR eR
    refine ⟨jR.comp g, ?_⟩
    intro x
    calc
      (jR.comp g) x = jR (g x) := rfl
      _ = jR (fR (eR x)) := congrArg jR (hg x)
      _ = functionalCompatibleFold hSrc
            (jL ∘ fL) (jR ∘ fR) hcompat (iR (eR x)) :=
        (functionalCompatibleFold_right hSrc
          (jL ∘ fL) (jR ∘ fR) hcompat (eR x)).symm
      _ = functionalCompatibleFold hSrc
            (jL ∘ fL) (jR ∘ fR) hcompat (e x) := by
        exact congrArg
          (functionalCompatibleFold hSrc (jL ∘ fL) (jR ∘ fR) hcompat)
          (Classical.choose_spec (hright x)).symm

end AllThoseRamseyClasses.Lifts
