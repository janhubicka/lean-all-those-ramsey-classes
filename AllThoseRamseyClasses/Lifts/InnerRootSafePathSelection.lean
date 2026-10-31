import AllThoseRamseyClasses.Lifts.SeparatorPaths

/-!
# A first-inner-root path in the retained source

The old source has two possibly incomparable vertex cuts: an inner
closed root U and an older outer root T. Let D be an ACTUAL connected
component after deleting U. Starting in D, follow any path avoiding
T. Every vertex z on that path is either still inside D, or z is
outside D and admits a T-avoiding path from some vertex of U back to z
with two additional properties:

* no vertex along this path enters D;
* on every path edge at least one endpoint lies outside U.

The second condition matters for genuine FUNCTIONAL free amalgams.
Even if both endpoints lie in the old complement of D, an old graph
edge with both endpoints in U can be witnessed by a high-arity tuple
also using a deleted D vertex. Such an edge need not survive in the
complement. The safe-path condition excludes exactly these false
reflections, and the companion SafeComplementPathTransfer lemma
reflects each safe edge through the actual full free-amalgam diagram.

All geometry in this module is on the existing literal Gaifman graph.
There is no finiteness assumption, inclusion T⊆U or U⊆T, and no
homomorphism-embedding injection or forbidden-family premise.
This module constructs the SAFE paths; subsequent work must still
relate the source complement carrier to the right-hand full
functional free-amalgam side after the literal flip.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.RelStructure

universe u v
variable {L : RelLanguage.{u}} {V : Type v}

/-- An old-source edge between retained vertices (outside the
selected U-component), avoiding an arbitrary older cut T,
is called safe when at least one endpoint is outside U.
Every safe edge survives a full functional replacement of D;
an edge with BOTH endpoints in U may not survive. -/
def innerRootSafeOutsideAdjacency
    (A : RelStructure L V)
    (T U : Set V)
    (d : {v : V // v ∉ U})
    (a b : {v : V // v ∉ T}) : Prop :=
  a.1 ∉ componentFrom A U d ∧
  b.1 ∉ componentFrom A U d ∧
  (a.1 ∉ U ∨ b.1 ∉ U) ∧
  outsideAdjacency A T a b

/-- Every path from a selected inner component D which avoids an
incomparable old outer cut T either stays inside D at its endpoint,
or reaches the endpoint through a SAFE path beginning at a vertex
of U outside T. This is the exact first-U-hitting invariant, proved
by induction on the original actual Gaifman path.

No false assertion that arbitrary induced subgraphs reflect all
higher-arity Gaifman edges is used. -/
theorem reachOutside_from_innerComponent_safeRootPath_or_inComponent
    (A : RelStructure L V)
    (T U : Set V)
    (d : {v : V // v ∉ U})
    (x y : {v : V // v ∉ T})
    (hx : x.1 ∈ componentFrom A U d)
    (h : ReachOutside A T x y) :
    y.1 ∈ componentFrom A U d ∨
      (y.1 ∉ componentFrom A U d ∧
        ∃ r : {v : V // v ∉ T},
          r.1 ∈ U ∧
            Relation.ReflTransGen
              (innerRootSafeOutsideAdjacency A T U d) r y) := by
  induction h with
  | refl =>
      exact Or.inl hx
  | @tail a b hpre hedge ih =>
      by_cases hbD : b.1 ∈ componentFrom A U d
      · exact Or.inl hbD
      · rcases ih with haD | ⟨haNotD, r, hrU, hrSafe⟩
        · have hbU : b.1 ∈ U := by
            by_contra hbNotU
            have hbFrom : b.1 ∈ componentFrom A U d :=
              componentFrom_step A U d haD hbNotU hedge
            exact hbD hbFrom
          exact Or.inr ⟨hbD, b, hbU, Relation.ReflTransGen.refl⟩
        · by_cases hbU : b.1 ∈ U
          · exact Or.inr ⟨hbD, b, hbU, Relation.ReflTransGen.refl⟩
          · have hStep : innerRootSafeOutsideAdjacency A T U d a b :=
              ⟨haNotD, hbD, Or.inr hbU, hedge⟩
            exact Or.inr ⟨hbD, r, hrU, hrSafe.tail hStep⟩

/-- In the non-inner-component case, the alternative is a genuine
safe path from the surviving inner ROOT, not merely a path in the
old source. Its root vertex avoids T and thus belongs to U \ T. -/
theorem reachOutside_retainedVertex_safeRootPath
    (A : RelStructure L V)
    (T U : Set V)
    (d : {v : V // v ∉ U})
    (x y : {v : V // v ∉ T})
    (hx : x.1 ∈ componentFrom A U d)
    (h : ReachOutside A T x y)
    (hy : y.1 ∉ componentFrom A U d) :
    ∃ r : {v : V // v ∉ T},
      r.1 ∈ U ∧
        Relation.ReflTransGen
          (innerRootSafeOutsideAdjacency A T U d) r y := by
  rcases reachOutside_from_innerComponent_safeRootPath_or_inComponent
      A T U d x y hx h with hD | ⟨_, hRoot⟩
  · exact False.elim (hy hD)
  · exact hRoot

end AllThoseRamseyClasses.Lifts
