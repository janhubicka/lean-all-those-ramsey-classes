import AllThoseRamseyClasses.Published.TrackEJointHybridFullRootRules

/-!
# Track E2: joint full-hybrid-root tags commute with exact weak induction

The 2019 Ramsey-picture proof tests the exact original vertex subset
S, not a generated function closure. A full hybrid tag can mention
the entire OLD root pattern, but every distinct root vertex is
already DISPLAYED among the tag tuple's input-prefix coordinates.

Consequently restricting a canonical joint full-root tag expansion
to S is identical to first inducing the base hybrid relation
structure on S and then forming its full-root tag expansion:
  jointTag(E.induce S) = jointTag(E).induce S.
Both split singleton-output tags and original complete-output-mask
tags satisfy the equality, independently of whether S is closed
under any primitive function.

We also lift all FULL hybrid embeddings to full joint-tag
embeddings, preserving and reflecting both tag families. The
proof is root-by-root with no hidden target completion, and
returns to the exact hybrid reduct on the same vertices.

This does NOT claim that arbitrary intermediate joint-tag pictures
are coherent native function structures, U-closed or Ramsey. In
particular, primitive complete output tuples and active domain
records remain induced from the original AMBIENT hybrid source.
-/

namespace StructuralRamsey.RelStructure

universe u v w z
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- A full root whose entire image is within S restricts to a
full embedding into the exact induced relational source E.induce S.
The carrier of the root and its vertex map remain unchanged. -/
private noncomputable def fullHybridRootIntoExactInduce
    {V : Type w} {X : Type z}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    {Root : RelStructure (L.splitMaskHybrid Parts) X}
    (S : Set V) (g : Embedding Root E)
    (h : ∀ x, g x ∈ S) :
    Embedding Root (E.induce S) where
  toFun := fun x => ⟨g x, h x⟩
  injective := by
    intro x y hxy
    apply g.injective
    exact congrArg Subtype.val hxy
  map_rel_iff := by
    intro R xs
    change E.rel R (g ∘ xs) ↔ Root.rel R xs
    exact g.map_rel_iff R xs

/-- Both full-hybrid-root tag families commute relation-by-relation
with restriction to one arbitrary original vertex set S. No output
is invented by recomputing the weak function values: all OLD
domain/mask/positive-incidence data is literally induced from E. -/
theorem splitMaskJointRootExpansion_induce_rel_iff
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V)
    (S : Set V)
    (R : (L.splitMaskJointRootLanguage Parts).Symbol)
    (xs : Fin ((L.splitMaskJointRootLanguage Parts).arity R) → S) :
    (splitMaskJointRootExpansion (E.induce S)).rel R xs ↔
      ((splitMaskJointRootExpansion E).induce S).rel R xs := by
  classical
  rcases R with R | R
  · rfl
  · rcases R with p | p
    · change
        (E.rel (Language.hybridSplitOutputSymbol p.input)
          (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root (E.induce S),
            ∀ i : Fin p.input.rootSize,
              xs i.castSucc = g i) ↔
        (E.rel (Language.hybridSplitOutputSymbol p.input)
          (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              (Subtype.val ∘ xs) i.castSucc = g i)
      constructor
      · rintro ⟨hOld, g, hp⟩
        refine ⟨hOld, (inclusion E S).comp g, ?_⟩
        intro i
        exact congrArg Subtype.val (hp i)
      · rintro ⟨hOld, g, hp⟩
        have hIn : ∀ i : Fin p.input.rootSize, g i ∈ S := by
          intro i
          rw [← hp i]
          exact (xs i.castSucc).2
        let gS : Embedding p.root (E.induce S) :=
          fullHybridRootIntoExactInduce S g hIn
        refine ⟨hOld, gS, ?_⟩
        intro i
        apply Subtype.ext
        exact hp i
    · change
        (E.rel (Language.hybridOriginalMaskOutputSymbol
            p.input p.mask) (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root (E.induce S),
            ∀ i : Fin p.input.rootSize,
              xs (Fin.castAdd p.mask.size i) = g i) ↔
        (E.rel (Language.hybridOriginalMaskOutputSymbol
            p.input p.mask) (Subtype.val ∘ xs) ∧
          ∃ g : Embedding p.root E,
            ∀ i : Fin p.input.rootSize,
              (Subtype.val ∘ xs) (Fin.castAdd p.mask.size i) = g i)
      constructor
      · rintro ⟨hOld, g, hp⟩
        refine ⟨hOld, (inclusion E S).comp g, ?_⟩
        intro i
        exact congrArg Subtype.val (hp i)
      · rintro ⟨hOld, g, hp⟩
        have hIn : ∀ i : Fin p.input.rootSize, g i ∈ S := by
          intro i
          rw [← hp i]
          exact (xs (Fin.castAdd p.mask.size i)).2
        let gS : Embedding p.root (E.induce S) :=
          fullHybridRootIntoExactInduce S g hIn
        refine ⟨hOld, gS, ?_⟩
        intro i
        apply Subtype.ext
        exact hp i

/-- One literal equality of relational structures on EXACTLY S.
Neither the vertex set nor the pre-existing active-domain masks
are modified by the new full-hybrid-root tag layer. -/
theorem splitMaskJointRootExpansion_induce_eq
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V)
    (S : Set V) :
    splitMaskJointRootExpansion (E.induce S) =
      (splitMaskJointRootExpansion E).induce S := by
  apply rel_injective
  funext R xs
  exact propext (splitMaskJointRootExpansion_induce_rel_iff E S R xs)

end StructuralRamsey.RelStructure

namespace StructuralRamsey.RelStructure.Embedding

universe u v w z
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]
variable {V : Type w} {W : Type z}
variable {E : RelStructure (L.splitMaskHybrid Parts) V}
variable {F : RelStructure (L.splitMaskHybrid Parts) W}

/-- Every FULL hybrid relational embedding lifts to a FULL
joint-tag embedding, including both split-incidence and original
complete-mask full-root tag relations. Both directions reflect the
root patterns; no target normality or U-closedness premise. -/
noncomputable def splitMaskJointRoot
    (f : Embedding E F) :
    Embedding (splitMaskJointRootExpansion E)
      (splitMaskJointRootExpansion F) where
  toFun := f
  injective := f.injective
  map_rel_iff := by
    intro R xs
    rcases R with R | R
    · exact f.map_rel_iff R xs
    · rcases R with p | p
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
        · rintro ⟨hF, gF, hpF⟩
          have hE : E.rel
              (Language.hybridSplitOutputSymbol p.input) xs :=
            (f.map_rel_iff (Language.hybridSplitOutputSymbol p.input)
              xs).mp hF
          let q : Fin p.input.rootSize → V := fun i => xs i.castSucc
          let gE : Embedding p.root E := {
            toFun := q
            injective := by
              intro i j hij
              apply gF.injective
              calc
                gF i = f (q i) := (hpF i).symm
                _ = f (q j) := congrArg f hij
                _ = gF j := hpF j
            map_rel_iff := by
              intro S ys
              have heq : f ∘ (q ∘ ys) = gF ∘ ys := by
                funext k
                exact hpF (ys k)
              calc
                E.rel S (q ∘ ys) ↔ F.rel S (f ∘ (q ∘ ys)) :=
                  (f.map_rel_iff S (q ∘ ys)).symm
                _ ↔ F.rel S (gF ∘ ys) := by rw [heq]
                _ ↔ p.root.rel S ys := gF.map_rel_iff S ys
          }
          exact ⟨hE, gE, fun _ => rfl⟩
        · rintro ⟨hE, gE, hpE⟩
          have hF : F.rel
              (Language.hybridSplitOutputSymbol p.input) (f ∘ xs) :=
            (f.map_rel_iff (Language.hybridSplitOutputSymbol p.input)
              xs).mpr hE
          refine ⟨hF, f.comp gE, ?_⟩
          intro i
          exact congrArg f (hpE i)
      · change
          (F.rel (Language.hybridOriginalMaskOutputSymbol
              p.input p.mask) (f ∘ xs) ∧
            ∃ g : Embedding p.root F,
              ∀ i : Fin p.input.rootSize,
                (f ∘ xs) (Fin.castAdd p.mask.size i) = g i) ↔
          (E.rel (Language.hybridOriginalMaskOutputSymbol
              p.input p.mask) xs ∧
            ∃ g : Embedding p.root E,
              ∀ i : Fin p.input.rootSize,
                xs (Fin.castAdd p.mask.size i) = g i)
        constructor
        · rintro ⟨hF, gF, hpF⟩
          have hE : E.rel
              (Language.hybridOriginalMaskOutputSymbol
                p.input p.mask) xs :=
            (f.map_rel_iff
              (Language.hybridOriginalMaskOutputSymbol
                p.input p.mask) xs).mp hF
          let q : Fin p.input.rootSize → V :=
            fun i => xs (Fin.castAdd p.mask.size i)
          let gE : Embedding p.root E := {
            toFun := q
            injective := by
              intro i j hij
              apply gF.injective
              calc
                gF i = f (q i) := (hpF i).symm
                _ = f (q j) := congrArg f hij
                _ = gF j := hpF j
            map_rel_iff := by
              intro S ys
              have heq : f ∘ (q ∘ ys) = gF ∘ ys := by
                funext k
                exact hpF (ys k)
              calc
                E.rel S (q ∘ ys) ↔ F.rel S (f ∘ (q ∘ ys)) :=
                  (f.map_rel_iff S (q ∘ ys)).symm
                _ ↔ F.rel S (gF ∘ ys) := by rw [heq]
                _ ↔ p.root.rel S ys := gF.map_rel_iff S ys
          }
          exact ⟨hE, gE, fun _ => rfl⟩
        · rintro ⟨hE, gE, hpE⟩
          have hF : F.rel
              (Language.hybridOriginalMaskOutputSymbol
                p.input p.mask) (f ∘ xs) :=
            (f.map_rel_iff
              (Language.hybridOriginalMaskOutputSymbol
                p.input p.mask) xs).mpr hE
          refine ⟨hF, f.comp gE, ?_⟩
          intro i
          exact congrArg f (hpE i)

/-- Forget the NEW outer split/mask full-root tags of any full
joint-tag embedding. Its map is literally the same function
and it still reflects the entire base hybrid relational language. -/
def splitMaskJointRootReduct
    {A : RelStructure (L.splitMaskJointRootLanguage Parts) V}
    {B : RelStructure (L.splitMaskJointRootLanguage Parts) W}
    (f : Embedding A B) :
    Embedding (RelStructure.splitMaskJointRootReduct A)
      (RelStructure.splitMaskJointRootReduct B) where
  toFun := f
  injective := f.injective
  map_rel_iff R xs := f.map_rel_iff (.inl R) xs

end StructuralRamsey.RelStructure.Embedding
