import AllThoseRamseyClasses.Published.InducedClosedLogicalDirection
import PartiteConstruction.Functional.PatternDecodedInducedMap2019
import PartiteConstruction.Structure.WeakHomomorphism

/-!
# Track E2: exact weak positive native incidence from a pattern-tag map

The ORIGINAL complete-output-mask language remembers each whole output
set but can forget the incidence of a particular surviving vertex when
other outputs leave the weak test. In contrast the previously verified
2019 input-equality-pattern graph language contains a separate POSITIVE
output tuple for each native function incidence.

This new bridge proves, for ANY tagged relational picture C, ANY exact
literal weak vertex set S, ANY canonical native target B and ANY map
f : S → B:

* an ordinary positive homomorphism of C.induce S into B's canonical
  pattern-tagged graph preserves every surviving decoded native
  function output on S;
* the same map is an entire native WEAK homomorphism of the decoded
  weak source, preserving both primitive relations and output incidences.

The proof reuses the independently verified exact-subset decoder
`RelStructure.Embedding.patternDecode_mem_induce`; it does NOT require
a FULL tagged embedding, function-closed S, image injection, or a
generated closure hull.

It does NOT prove the stronger ambient-relative native HE condition:
equality of complete target fibres on inputs closed inside S and
protection of all genuine FULL ambient irreducibles are separate.
It also does not build the remaining ordered E2 sparse Ramsey control.
-/

namespace AllThoseRamseyClasses.Published

open StructuralRamsey
open StructuralRamsey.RelStructure
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}} {V W : Type v}

/-- Only POSITIVE OLD pattern-graph preservation is needed to carry
each decoded function output; the existing embedding version can be
weakened to an ordinary relational homomorphism on the same map. -/
theorem patternDecode_output_of_positive_patternGraph_hom
    (E : RelStructure (L.patternGraph) V)
    (Base : Structure L W)
    (f : V → W)
    (hf : E.IsHomomorphism Base.patternGraph f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → V) (y : V)
    (hy : y ∈ (Structure.patternDecode E).func F xs) :
    f y ∈ Base.func F (f ∘ xs) := by
  obtain ⟨m, r, hr, root, _hInj, hFact, _hDom, hGraph⟩ := hy
  let p : Language.FunctionInputPattern L :=
    { symbol := F, rootSize := m, argMap := r, onto := hr }
  have hTarget : Base.patternGraph.rel (.inr (.inr p))
      (f ∘ Structure.funcTuple root y) :=
    hf (.inr (.inr p)) (Structure.funcTuple root y) hGraph
  have hTuple := Structure.comp_funcTuple f root y
  have hTarget' : Base.patternGraph.rel (.inr (.inr p))
      (Structure.funcTuple (f ∘ root) (f y)) :=
    hTuple ▸ hTarget
  have hExpanded :
      Function.Injective
        (fun i : Fin m =>
          (Structure.funcTuple (f ∘ root) (f y)) i.castSucc) ∧
      (Structure.funcTuple (f ∘ root) (f y)) (Fin.last m) ∈
        Base.func F
          ((fun i : Fin m =>
            (Structure.funcTuple (f ∘ root) (f y)) i.castSucc) ∘ r) :=
    hTarget'
  have hGraphTarget :
      Function.Injective (f ∘ root) ∧
        f y ∈ Base.func F ((f ∘ root) ∘ r) := by
    simpa only [Structure.funcTuple_castSucc,
      Structure.funcTuple_last] using hExpanded
  have hArgs : (f ∘ root) ∘ r = f ∘ xs := by
    funext i
    exact congrArg f (hFact i).symm
  rw [hArgs] at hGraphTarget
  exact hGraphTarget.2

/-- A tagged positive map on the ORIGINAL exact S preserves every
decoded output that survives the native weak restriction, even if
other outputs of the SAME primitive application leave S. -/
theorem patternDecode_exactWeak_output_of_positive_taggedHom
    (C : RelStructure (L.patternTag) V)
    (S : Set V)
    (Base : Structure L W)
    (f : S → W)
    (hf : (C.induce S).IsHomomorphism
      (RelStructure.patternTagExpansion Base.patternGraph) f)
    (F : L.FuncSymbol)
    (xs : Fin (L.funcArity F) → S) (y : S)
    (hy : y ∈ ((Structure.patternDecode
      (RelStructure.patternTagReduct C)).weakInduce S).func F xs) :
    f y ∈ Base.func F (f ∘ xs) := by
  have hOld :
      (RelStructure.patternTagReduct (C.induce S)).IsHomomorphism
        Base.patternGraph f := by
    intro symbol t ht
    exact hf (.inl symbol) t ht
  have hAmbient :
      y.1 ∈ (Structure.patternDecode
        (RelStructure.patternTagReduct C)).func F
          (Subtype.val ∘ xs) :=
    (Structure.weakInduce_func
      (Structure.patternDecode
        (RelStructure.patternTagReduct C)) S F xs y).mp hy
  have hInduced :
      y ∈ (Structure.patternDecode
        (RelStructure.patternTagReduct (C.induce S))).func F xs :=
    RelStructure.Embedding.patternDecode_mem_induce
      (C := C) S F (Subtype.val ∘ xs)
      (fun i => (xs i).2) y.1 y.2 hAmbient
  exact patternDecode_output_of_positive_patternGraph_hom
    (RelStructure.patternTagReduct (C.induce S))
    Base f hOld F xs y hInduced

/-- The complete native WEAK homomorphism bridge: ALL original
relations and ALL surviving weak function incidences are mapped
positively on the SAME exact vertex set S. There is no total-fibre
or protected-test claim. -/
theorem patternDecode_exactWeak_weakHom_of_positive_taggedHom
    (C : RelStructure (L.patternTag) V)
    (S : Set V)
    (Base : Structure L W)
    (f : S → W)
    (hf : (C.induce S).IsHomomorphism
      (RelStructure.patternTagExpansion Base.patternGraph) f) :
    ((Structure.patternDecode
      (RelStructure.patternTagReduct C)).weakInduce S).IsWeakHomomorphism
      Base f := by
  constructor
  · intro R xs hx
    exact hf (.inl (.inl R)) xs hx
  · intro F xs y hy
    exact patternDecode_exactWeak_output_of_positive_taggedHom
      C S Base f hf F xs y hy

end AllThoseRamseyClasses.Published
