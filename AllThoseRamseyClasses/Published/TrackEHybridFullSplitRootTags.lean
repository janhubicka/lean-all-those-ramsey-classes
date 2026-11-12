import AllThoseRamseyClasses.Published.TrackEHybridSignatureFinite
import PartiteConstruction.Functional.PatternClosureTags2019
import PartiteConstruction.Ramsey.ClosureDescription2019

/-!
# Track E2: FULL HYBRID ROOT tags for each positive split-function input

The canonical hybrid source of Track E2 #1037 already records both
original complete-value masks and split per-output-part incidences.
Its old fresh tags were produced separately in their respective
languages, however, so their root names do NOT record the complete
HYBRID induced root structure. A 2019 closure rule must use the full
root of its actual relational language.

We introduce a new fresh tag for every:
* singleton split primitive function/input equality pattern;
* strictly positive distinct-input root size;
* FULL HYBRID relational structure on that root carrier, with
  a true corresponding split-function domain relation.

The new relation holds over one output tuple when the split old
positive output relation holds and the full hybrid root embeds
exactly on the displayed input prefix. The root has a spanning
active input-domain relation, hence is ordinarily irreducible.
Canonical full hybrid embeddings lift to these new tagged symbols
and forget back, retaining EXACTLY their vertex maps.

This module proves the language, full-root closure description,
root irreducibility and full-embedding functor. It does NOT claim
that arbitrary hybrid targets are U-closed, or that a 2019 sparse
construction for this new enlarged language has been established.
The parallel original complete-mask hybrid-root rules remain separate.
-/

namespace StructuralRamsey

universe u v w z

namespace Language

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The positive old graph of one split (F,q) input is a symbol
of the COMPLETE HYBRID source language, with unchanged input equality
pattern and one displayed output vertex. -/
def hybridSplitOutputSymbol
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inr (.inl (.inl (.inr (.inr p))))

/-- The domain of the SAME split (F,q) input is recorded on the
distinct input root, regardless of outputs forgotten by a weak test. -/
def hybridSplitDomainSymbol
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inr (.inl (.inl (.inr (.inl p))))

/-- The original complete-mask symbol family is retained disjointly.
This syntax helper prevents confusing an original OLD mask with the
singleton split pattern on the same original vertices. -/
def hybridOriginalOldSymbol
    (R : (L.wholeMaskTagLanguage Parts).Symbol) :
    (L.splitMaskHybrid Parts).Symbol :=
  .inl R

/-- A genuine positive full hybrid root for a split-function tag.
The whole induced HYBRID relational pattern, including all old masks,
split graph/domain data and unary parts on the distinct input root,
belongs to the tag name. -/
structure SplitMaskFullRootPattern
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] where
  input : FunctionInputPattern (L.outputPartIndexed Parts)
  positive : 0 < input.rootSize
  root : RelStructure (L.splitMaskHybrid Parts) (Fin input.rootSize)
  hasDomain : root.rel (hybridSplitDomainSymbol input) id

/-- Keep all existing hybrid symbols and add one FRESH closure
relation for each complete active hybrid root. -/
def splitMaskHybridFullRootLanguage
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] :
    RelLanguage.{max u v} where
  Symbol := (L.splitMaskHybrid Parts).Symbol ⊕
    SplitMaskFullRootPattern L Parts
  arity
    | .inl R => (L.splitMaskHybrid Parts).arity R
    | .inr p => p.input.rootSize + 1

end Language

namespace RelStructure

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w}

/-- Canonical full HYBRID root tag. An output tag holds precisely
when its split positive OLD function graph tuple is present and
the FULL specified hybrid input root embeds on its exact prefix. -/
def splitMaskHybridFullRootExpansion
    (E : RelStructure (L.splitMaskHybrid Parts) V) :
    RelStructure (L.splitMaskHybridFullRootLanguage Parts) V where
  rel
    | .inl R, xs => E.rel R xs
    | .inr p, xs =>
        E.rel (Language.hybridSplitOutputSymbol p.input) xs ∧
          ∃ e : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs i.castSucc = e i

/-- The full-root tag is an additional symbol layer: forgetting it
returns the EXACT same hybrid relation interpretations. -/
def splitMaskHybridFullRootReduct
    (E : RelStructure (L.splitMaskHybridFullRootLanguage Parts) V) :
    RelStructure (L.splitMaskHybrid Parts) V where
  rel R xs := E.rel (.inl R) xs

end RelStructure

namespace RelStructure.Embedding

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w} {W : Type z}
variable {E : RelStructure (L.splitMaskHybrid Parts) V}
variable {F : RelStructure (L.splitMaskHybrid Parts) W}

/-- A full relational embedding of the WHOLE hybrid language induces
a full embedding after adding fresh full-hybrid-root split tags.
The statement has no relation/function closure assumption. -/
noncomputable def splitMaskHybridFullRoot
    (f : Embedding E F) :
    Embedding (splitMaskHybridFullRootExpansion E)
      (splitMaskHybridFullRootExpansion F) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | p
    · exact f.map_rel_iff R xs
    · change
        (F.rel (Language.hybridSplitOutputSymbol p.input) (f ∘ xs) ∧
          ∃ g : Embedding p.root F,
            ∀ i : Fin p.input.rootSize,
              (f ∘ xs) i.castSucc = g i) ↔
        (E.rel (Language.hybridSplitOutputSymbol p.input) xs ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              xs i.castSucc = g i)
      constructor
      · rintro ⟨hF, gF, hPrefixF⟩
        have hE : E.rel
            (Language.hybridSplitOutputSymbol p.input) xs :=
          (f.map_rel_iff (Language.hybridSplitOutputSymbol p.input)
            xs).mp hF
        let q : Fin p.input.rootSize → V :=
          fun i => xs i.castSucc
        let gE : Embedding p.root E := {
          toFun := q
          injective := by
            intro i j hij
            apply gF.injective
            calc
              gF i = f (q i) := (hPrefixF i).symm
              _ = f (q j) := congrArg f hij
              _ = gF j := hPrefixF j
          map_rel_iff := by
            intro S ys
            have hEq : f ∘ (q ∘ ys) = gF ∘ ys := by
              funext k
              exact hPrefixF (ys k)
            calc
              E.rel S (q ∘ ys) ↔ F.rel S (f ∘ (q ∘ ys)) :=
                (f.map_rel_iff S (q ∘ ys)).symm
              _ ↔ F.rel S (gF ∘ ys) := by rw [hEq]
              _ ↔ p.root.rel S ys := gF.map_rel_iff S ys
        }
        exact ⟨hE, gE, fun _ => rfl⟩
      · rintro ⟨hE, gE, hPrefixE⟩
        have hF : F.rel
            (Language.hybridSplitOutputSymbol p.input) (f ∘ xs) :=
          (f.map_rel_iff (Language.hybridSplitOutputSymbol p.input)
            xs).mpr hE
        refine ⟨hF, f.comp gE, ?_⟩
        intro i
        exact congrArg f (hPrefixE i)

/-- Forgetting the new full-root split tags of a FULL embedding
recovers a full embedding of the OLD HYBRID reducts unchanged. -/
def splitMaskHybridFullRootReduct
    {A : RelStructure (L.splitMaskHybridFullRootLanguage Parts) V}
    {B : RelStructure (L.splitMaskHybridFullRootLanguage Parts) W}
    (f : Embedding A B) :
    Embedding (RelStructure.splitMaskHybridFullRootReduct A)
      (RelStructure.splitMaskHybridFullRootReduct B) where
  toFun := f
  injective := f.injective
  map_rel_iff R xs := f.map_rel_iff (.inl R) xs

end RelStructure.Embedding

namespace Language.SplitMaskFullRootPattern

variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The 2019 closure rule for one full HYBRID root. Its root is
irreducible because the active domain relation spans every
distinct input-root coordinate, even when the original argument
tuple repeats a vertex. Positive input size is explicit. -/
def closureRule (p : SplitMaskFullRootPattern L Parts) :
    RelStructure.ClosureRule (L.splitMaskHybridFullRootLanguage Parts) where
  symbol := .inr p
  rootSize := p.input.rootSize
  rootPositive := p.positive
  rootStrict := Nat.lt_succ_self _
  root := RelStructure.splitMaskHybridFullRootExpansion p.root
  rootIrreducible := by
    intro x y hxy
    refine ⟨.inl (hybridSplitDomainSymbol p.input),
      (fun i : Fin p.input.rootSize => i), x, y, ?_, rfl, rfl⟩
    exact p.hasDomain

end Language.SplitMaskFullRootPattern

namespace Language

/-- The literal 2019 closure description of all new FULL HYBRID
split-function root tags, one rule for each active full hybrid
root pattern. The complete OLD mask closure rules are not included
yet; they require their own full hybrid root patterns. -/
def splitMaskHybridSplitClosureRules
    (L : Language.{u}) (Parts : Type v) [Fintype Parts] :
    RelStructure.ClosureDescription
      (L.splitMaskHybridFullRootLanguage Parts) :=
  Set.range SplitMaskFullRootPattern.closureRule

end Language

end StructuralRamsey
