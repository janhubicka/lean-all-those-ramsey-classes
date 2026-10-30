import PartiteConstruction.Functional.WeakInvariant

/-!
# A source-side criterion forcing closed EHN target images

A genuine EHN map is full on every FULL irreducible source test.
Thus, if every complete source input tuple of a native function
symbol lies in SOME irreducible full test, a target function
applied to image inputs cannot produce a vertex outside the
raw source image.

This covers set-valued functions of arbitrary arity. It makes
explicit the missing assumption behind the published unqualified
"replace the forbidden witness by its image" shortcut. For
binary or higher-arity functions, an input tuple may use two
independent source components and may not lie in ANY irreducible
closed test; this is exactly why the unqualified shortcut fails.

The property concerns full irreducible STRUCTURES and full
source embeddings, not a relational graph encoding or the
false claim that all source tuples are irreducible themselves.
The separate unary one-generator result is a useful sufficient
case of the input-cover property, without needing a global bound
on relations or root widths.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Every input tuple of every original NATIVE function symbol
lies in the image of a FULL embedding of some irreducible
source substructure. The test may contain other vertices,
including the generated function outputs and nullary constants.

This SOURCE property does not depend on the chosen target map. -/
def FunctionInputTuplesCoveredByIrreducibleTests
    {V : Type v} (A : Structure L V) : Prop :=
  ∀ (F : L.FuncSymbol) (xs : Fin (L.funcArity F) → V),
    ∃ (U : Type v) (E : Structure L U),
      E.Irreducible ∧
      ∃ (e : Structure.Embedding E A)
        (ys : Fin (L.funcArity F) → U),
        ∀ i, e (ys i) = xs i

/-- If every native SOURCE function-input tuple lies in a
genuine full irreducible source test, then EVERY weak EHN
target range is function-closed, with no assumption of
injectivity on the source or root images.

Indeed, choose preimages of a target input tuple, cover those
source inputs by an irreducible E, and invoke the FULL EHN
embedding g:E→Target. Its exact native function-fibre equality
forces every target output on that tuple to equal g(y)=f(e(y))
for some actual SOURCE vertex e(y). -/
theorem ehn_range_isClosed_of_irreducibleInputCover
    {V W : Type v}
    (A : Structure L V) (B : Structure L W)
    (f : V → W)
    (hf : A.IsEHNHomomorphismEmbedding B f)
    (hCover : FunctionInputTuplesCoveredByIrreducibleTests A) :
    B.IsClosed (Set.range f) := by
  classical
  intro F zs hzs out hout
  let xs : Fin (L.funcArity F) → V :=
    fun i => Classical.choose (hzs i)
  have hArg : ∀ i : Fin (L.funcArity F),
      f (xs i) = zs i := by
    intro i
    exact Classical.choose_spec (hzs i)
  obtain ⟨U, E, hIrr, e, ys, he⟩ := hCover F xs
  obtain ⟨g, hg⟩ := hf.2 E hIrr e
  have hArgs : g ∘ ys = zs := by
    funext i
    calc
      g (ys i) = f (e (ys i)) := hg (ys i)
      _ = f (xs i) := congrArg f (he i)
      _ = zs i := hArg i
  have hValue : out ∈ B.func F (g ∘ ys) := by
    rw [hArgs]
    exact hout
  have hImage : out ∈ imageSet g (E.func F ys) := by
    rw [g.map_func F ys]
    exact hValue
  obtain ⟨y, hy, hOut⟩ := hImage
  exact ⟨e y, (hg y).symm.trans hOut⟩

end AllThoseRamseyClasses.Lifts
