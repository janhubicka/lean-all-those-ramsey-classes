import AllThoseRamseyClasses.Published.TrackEHybridSplitDomainPatternTransport
import PartiteConstruction.Iterated.LocalTreeLike
import PartiteConstruction.Structure.Relationalize

/-!
# Track E2: same-value split output tuples across exact input equality patterns

For a primitive function F and fixed output part q, the actual
native (F,q)-value cannot depend on the injective enumeration of
the distinct input vertices. The previous original OLD domain
cross-pattern laws ensure the same domain masks under two such
presentations. They do NOT themselves force POSITIVE singleton
split output tuples to name the same output vertex.

We formalize the separate positive-output transport condition:
if two injective distinct-input presentations describe the SAME
primitive argument tuple, a visible (F,q)-output at vertex y in
the first presentation is also visible at the SAME y in the
second presentation. This is a necessary target-decoding invariant
not implied just by same output-PART sets.

The law holds for every canonical genuinely native partite source,
survives exact induced weak restriction, and survives TRUE FULL
relational free amalgamation. The free-amalgam argument factors
the second root into whichever side contains the first positive
output tuple: both roots enumerate precisely the same set of
primitive input vertices, and the output vertex is already in
the first side. No extra vertex or whole-value witness is formed.

This closes an independent cross-PATTERN positive-incidence
normality law, but not cross-MASK whole-value consistency or
the finite-family two-pass sparse Ramsey theorem.
-/

namespace StructuralRamsey.RelStructure

open StructuralRamsey
open StructuralRamsey.Language
open StructuralRamsey.FunctionalPartite

universe u v w
variable {L : Language.{u}} {Parts : Type v} [Fintype Parts]

/-- The SAME visible singleton split output y of part q is retained
across every injective distinct-root representation of the SAME
original primitive argument tuple. The original argument maps may
repeat primitive input vertices, and nullary arities are allowed. -/
def HybridSplitOutputPatternTransport
    {V : Type w}
    (E : RelStructure (L.splitMaskHybrid Parts) V) : Prop :=
  ∀ (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → V)
    (rootB : Fin n → V)
    (q : Parts) (y : V),
    Function.Injective rootB →
    rootA ∘ r = rootB ∘ s →
    E.rel (hybridSplitOutputSymbol
      (splitMaskInputAtPart
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) q))
      (Structure.funcTuple rootA y) →
    E.rel (hybridSplitOutputSymbol
      (splitMaskInputAtPart
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) q))
      (Structure.funcTuple rootB y)

/-- Canonical native singleton split fibres depend only on the
ACTUAL original F-argument tuple and the selected part q, not on
which injective equality-pattern root enumerates the inputs. -/
theorem canonicalHybrid_splitOutputPatternTransport
    {V : Type w}
    (A : FunctionalPartite.System L Parts V) :
    HybridSplitOutputPatternTransport A.splitMaskHybrid := by
  intro F m n r s hr hs rootA rootB q y hInjB hArgs hPos
  have hSource :
      Function.Injective rootA ∧
      y ∈ A.splitOutputParts.toStructure.func
        (ULift.up F, q) (rootA ∘ r) := by
    change Function.Injective
      (fun i : Fin m =>
        (Structure.funcTuple rootA y) i.castSucc) ∧
      (Structure.funcTuple rootA y) (Fin.last m) ∈
      A.splitOutputParts.toStructure.func (ULift.up F, q)
        ((fun i : Fin m =>
          (Structure.funcTuple rootA y) i.castSucc) ∘ r) at hPos
    simpa only [Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using hPos
  have hTarget :
      Function.Injective rootB ∧
      y ∈ A.splitOutputParts.toStructure.func
        (ULift.up F, q) (rootB ∘ s) := by
    refine ⟨hInjB, ?_⟩
    rw [← hArgs]
    exact hSource.2
  change Function.Injective
    (fun i : Fin n =>
      (Structure.funcTuple rootB y) i.castSucc) ∧
    (Structure.funcTuple rootB y) (Fin.last n) ∈
    A.splitOutputParts.toStructure.func (ULift.up F, q)
      ((fun i : Fin n =>
        (Structure.funcTuple rootB y) i.castSucc) ∘ s)
  simpa only [Structure.funcTuple_castSucc,
    Structure.funcTuple_last] using hTarget

/-- Any literal exact induced weak set inherits the SAME-VERTEX
positive split output cross-pattern law. If the output vertex
survives the weak cut, it is not replaced by a different value. -/
theorem HybridSplitOutputPatternTransport.induce
    {V : Type w}
    {E : RelStructure (L.splitMaskHybrid Parts) V}
    (h : HybridSplitOutputPatternTransport E)
    (S : Set V) :
    HybridSplitOutputPatternTransport (E.induce S) := by
  intro F m n r s hr hs rootA rootB q y hInjB hArgs hPos
  have hInjBV : Function.Injective (Subtype.val ∘ rootB) := by
    intro i j hij
    apply hInjB
    exact Subtype.ext hij
  have hArgsV :
      (Subtype.val ∘ rootA) ∘ r =
        (Subtype.val ∘ rootB) ∘ s := by
    funext i
    exact congrArg Subtype.val (congrFun hArgs i)
  let symA := hybridSplitOutputSymbol
    (splitMaskInputAtPart
      (⟨F, m, r, hr⟩ : FunctionInputPattern L) q)
  let symB := hybridSplitOutputSymbol
    (splitMaskInputAtPart
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) q)
  have hRelA :
      E.rel symA
        (Structure.funcTuple (Subtype.val ∘ rootA) y.1) := by
    change E.rel symA (Subtype.val ∘
      Structure.funcTuple rootA y) at hPos
    have hTuple := Structure.comp_funcTuple Subtype.val rootA y
    exact
      (congrArg (fun xs : Fin (m + 1) → V =>
        E.rel symA xs) hTuple).mp hPos
  have hRelB :
      E.rel symB
        (Structure.funcTuple (Subtype.val ∘ rootB) y.1) :=
    h F m n r s hr hs
      (Subtype.val ∘ rootA) (Subtype.val ∘ rootB)
      q y.1 hInjBV hArgsV hRelA
  change E.rel symB (Subtype.val ∘
    Structure.funcTuple rootB y)
  have hTuple := Structure.comp_funcTuple Subtype.val rootB y
  exact
    (congrArg (fun xs : Fin (n + 1) → V =>
      E.rel symB xs) hTuple).mpr hRelB

/-- One FULL embedded-side transport: the first positive
output tuple already lies inside a side. Every vertex of the
alternative exact input root is among that same original
primitive input tuple, and the SAME output y is also on the side.
Transport there and map the positive tuple back into the whole. -/
private theorem splitOutputPattern_fromSide
    {X Y : Type w}
    {Side : RelStructure (L.splitMaskHybrid Parts) X}
    {Whole : RelStructure (L.splitMaskHybrid Parts) Y}
    (e : Embedding Side Whole)
    (hSide : HybridSplitOutputPatternTransport Side)
    (F : L.FuncSymbol) (m n : ℕ)
    (r : Fin (L.funcArity F) → Fin m)
    (s : Fin (L.funcArity F) → Fin n)
    (hr : Function.Surjective r)
    (hs : Function.Surjective s)
    (rootA : Fin m → Y)
    (rootB : Fin n → Y)
    (q : Parts) (y : Y)
    (x : Fin (m + 1) → X)
    (hSidePos : Side.rel (hybridSplitOutputSymbol
      (splitMaskInputAtPart
        (⟨F, m, r, hr⟩ : FunctionInputPattern L) q)) x)
    (hFirstTuple : Structure.funcTuple rootA y = e ∘ x)
    (hInjB : Function.Injective rootB)
    (hArgs : rootA ∘ r = rootB ∘ s) :
    Whole.rel (hybridSplitOutputSymbol
      (splitMaskInputAtPart
        (⟨F, n, s, hs⟩ : FunctionInputPattern L) q))
      (Structure.funcTuple rootB y) := by
  classical
  let sideA : Fin m → X := fun i => x i.castSucc
  let out : X := x (Fin.last m)
  have hA : rootA = e ∘ sideA := by
    funext i
    calc
      rootA i = (Structure.funcTuple rootA y) i.castSucc :=
        (Structure.funcTuple_castSucc rootA y i).symm
      _ = e (x i.castSucc) := congrFun hFirstTuple i.castSucc
      _ = e (sideA i) := rfl
  have hY : y = e out := by
    calc
      y = (Structure.funcTuple rootA y) (Fin.last m) :=
        (Structure.funcTuple_last rootA y).symm
      _ = e (x (Fin.last m)) := congrFun hFirstTuple (Fin.last m)
  let sideB : Fin n → X :=
    fun j => sideA (r (Classical.choose (hs j)))
  have hB : rootB = e ∘ sideB := by
    funext j
    calc
      rootB j =
          rootB (s (Classical.choose (hs j))) :=
        (congrArg rootB (Classical.choose_spec (hs j))).symm
      _ = rootA (r (Classical.choose (hs j))) :=
        (congrFun hArgs (Classical.choose (hs j))).symm
      _ = e (sideA (r (Classical.choose (hs j)))) :=
        congrFun hA (r (Classical.choose (hs j)))
      _ = e (sideB j) := rfl
  have hSideBInj : Function.Injective sideB := by
    intro i j hij
    apply hInjB
    calc
      rootB i = e (sideB i) := congrFun hB i
      _ = e (sideB j) := congrArg e hij
      _ = rootB j := (congrFun hB j).symm
  have hSideArgs : sideA ∘ r = sideB ∘ s := by
    funext i
    apply e.injective
    calc
      e (sideA (r i)) = rootA (r i) :=
        (congrFun hA (r i)).symm
      _ = rootB (s i) := congrFun hArgs i
      _ = e (sideB (s i)) := congrFun hB (s i)
  have hSideFull :
      Side.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, m, r, hr⟩ : FunctionInputPattern L) q))
        (Structure.funcTuple sideA out) := by
    rw [Structure.funcTuple_eta x]
    exact hSidePos
  have hTargetSide :
      Side.rel (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, n, s, hs⟩ : FunctionInputPattern L) q))
        (Structure.funcTuple sideB out) :=
    hSide F m n r s hr hs sideA sideB
      q out hSideBInj hSideArgs hSideFull
  let symB := hybridSplitOutputSymbol
    (splitMaskInputAtPart
      (⟨F, n, s, hs⟩ : FunctionInputPattern L) q)
  have hWholeSide :
      Whole.rel symB (e ∘ Structure.funcTuple sideB out) :=
    (e.map_rel_iff symB (Structure.funcTuple sideB out)).mpr
      hTargetSide
  have hTuple :
      Structure.funcTuple rootB y =
        e ∘ Structure.funcTuple sideB out := by
    calc
      Structure.funcTuple rootB y =
          Structure.funcTuple (e ∘ sideB) (e out) := by
        rw [← hB, ← hY]
      _ = e ∘ Structure.funcTuple sideB out :=
        (Structure.comp_funcTuple e.toFun sideB out).symm
  exact
    (congrArg (fun xs : Fin (n + 1) → Y =>
      Whole.rel symB xs) hTuple).mpr hWholeSide

/-- TRUE FULL free amalgamation preserves positive split SAME-VALUE
cross-pattern transport. A visible output comes wholly from one
side; both presentations of the same primitive input enumerate
only vertices of that side, and the output is not duplicated. -/
theorem HybridSplitOutputPatternTransport.freeAmalgam
    {H E F C : Type w}
    {Root : RelStructure (L.splitMaskHybrid Parts) H}
    {Left : RelStructure (L.splitMaskHybrid Parts) E}
    {Right : RelStructure (L.splitMaskHybrid Parts) F}
    {Whole : RelStructure (L.splitMaskHybrid Parts) C}
    {sL : Embedding Root Left} {sR : Embedding Root Right}
    {iL : Embedding Left Whole} {iR : Embedding Right Whole}
    (hFree : IsFreeAmalgam sL sR iL iR)
    (hLeft : HybridSplitOutputPatternTransport Left)
    (hRight : HybridSplitOutputPatternTransport Right) :
    HybridSplitOutputPatternTransport Whole := by
  intro F m n r s hr hs rootA rootB q y hInjB hArgs hOld
  rcases (hFree.rel_iff
      (hybridSplitOutputSymbol
        (splitMaskInputAtPart
          (⟨F, m, r, hr⟩ : FunctionInputPattern L) q))
      (Structure.funcTuple rootA y)).mp hOld with
    ⟨x, hx, hFirst⟩ | ⟨x, hx, hFirst⟩
  · exact splitOutputPattern_fromSide iL hLeft
      F m n r s hr hs rootA rootB q y x hx
      hFirst hInjB hArgs
  · exact splitOutputPattern_fromSide iR hRight
      F m n r s hr hs rootA rootB q y x hx
      hFirst hInjB hArgs

end StructuralRamsey.RelStructure
