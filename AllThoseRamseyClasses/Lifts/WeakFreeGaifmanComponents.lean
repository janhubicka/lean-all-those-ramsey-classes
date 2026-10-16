import AllThoseRamseyClasses.Lifts.WeakSourceFreeAmalgamPartition
import AllThoseRamseyClasses.Lifts.WeakFunctionalGaifmanProjection
import AllThoseRamseyClasses.Lifts.FunctionalGaifmanCuts

/-!
# Gaifman components of a weak source cannot cross free-amalgam sides

The 2019 lift strong-amalgamation argument first pulls the full common
root of an actual functional free amalgam back under a potentially
NONINJECTIVE homomorphism-embedding. A source Gaifman component after
deleting that preimage cannot contain vertices mapped to both
exclusive sides of the target.

This is proved from the target's real relational and functional
free-amalgam incidences, together with positive-incidence preservation
of a WEAK functional homomorphism. No injectivity, surjectivity,
or reflection of undefined function applications is assumed.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}
variable {H E F W U : Type v}
variable {Root : Structure L H}
variable {Left : Structure L E} {Right : Structure L F}
variable {Whole : Structure L W} {Source : Structure L U}
variable {sL : Structure.Embedding Root Left}
variable {sR : Structure.Embedding Root Right}
variable {iL : Structure.Embedding Left Whole}
variable {iR : Structure.Embedding Right Whole}

/-- Every positive tuple in the FULL RELATIONAL GRAPH of a functional
free amalgam lies entirely on one side, including its function output
coordinate. This is stronger than merely checking original relations. -/
theorem functionalFreeAmalgam_graphTuple_side
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (R : L.graph.Symbol) (xs : Fin (L.graph.arity R) → W)
    (hxs : Whole.graph.rel R xs) :
    (∀ j, ∃ a : E, xs j = iL a) ∨
      (∀ j, ∃ b : F, xs j = iR b) := by
  cases R with
  | inl S =>
      rcases (hfree.rel_iff S xs).mp hxs with
        ⟨as, _, heq⟩ | ⟨bs, _, heq⟩
      · left
        intro j
        exact ⟨as j, congrFun heq j⟩
      · right
        intro j
        exact ⟨bs j, congrFun heq j⟩
  | inr G =>
      change xs (Fin.last (L.funcArity G)) ∈
        Whole.func G (fun j => xs j.castSucc) at hxs
      rcases (hfree.func_iff G
          (fun j => xs j.castSucc)
          (xs (Fin.last (L.funcArity G)))).mp hxs with
        ⟨as, b, _, heq, houtput⟩ |
        ⟨as, b, _, heq, houtput⟩
      · left
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · exact ⟨b, houtput⟩
        · exact ⟨as k, congrFun heq k⟩
      · right
        intro j
        refine Fin.lastCases ?_ (fun k => ?_) j
        · exact ⟨b, houtput⟩
        · exact ⟨as k, congrFun heq k⟩

/-- A source vertex in the exclusive RIGHT region cannot also have
a target image in the left side, by the exact overlap certificate. -/
theorem weakFreeRightPart_not_left
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) {y : U}
    (hy : y ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (a : E) : f y ≠ iL a := by
  intro ha
  obtain ⟨⟨b, hb⟩, hnotRoot⟩ := hy
  have hab : iL a = iR b := ha.symm.trans hb
  obtain ⟨r, hrL, _hrR⟩ := (hfree.overlap a b).mp hab
  apply hnotRoot
  refine ⟨r, ?_⟩
  change iL (sL r) = f y
  calc
    iL (sL r) = iL a := congrArg iL hrL.symm
    _ = f y := ha.symm

/-- A source vertex in the exclusive LEFT region cannot also have
a target image in the right side. -/
theorem weakFreeLeftPart_not_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) {x : U}
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (b : F) : f x ≠ iR b := by
  intro hb
  obtain ⟨⟨a, ha⟩, hnotRoot⟩ := hx
  have hab : iL a = iR b := ha.symm.trans hb
  obtain ⟨r, hrL, _hrR⟩ := (hfree.overlap a b).mp hab
  apply hnotRoot
  refine ⟨r, ?_⟩
  change iL (sL r) = f x
  calc
    iL (sL r) = iL a := congrArg iL hrL.symm
    _ = f x := ha.symm

/-- Positive target incidences never connect the images of a
left-exclusive and a right-exclusive source vertex. -/
theorem weakFreePartition_target_no_cross_edge
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) {x y : U}
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f) :
    ¬ GaifmanAdjacent Whole.graph (f x) (f y) := by
  rintro ⟨_, R, xs, i, j, htuple, hxi, hyj⟩
  rcases functionalFreeAmalgam_graphTuple_side hfree R xs htuple with
    hLeft | hRight
  · obtain ⟨a, ha⟩ := hLeft j
    exact weakFreeRightPart_not_left hfree f hy a (hyj.symm.trans ha)
  · obtain ⟨b, hb⟩ := hRight i
    exact weakFreeLeftPart_not_right hfree f hx b (hxi.symm.trans hb)

/-- A weak source Gaifman edge cannot join the two exclusive
target regions. It can collapse only within a single region. -/
theorem weakFreePartition_source_no_cross_edge
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {x y : U}
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f) :
    ¬ GaifmanAdjacent Source.graph x y := by
  intro hedge
  rcases weakFunctionalGaifmanAdjacent_map hf hedge with heq | hedge'
  · obtain ⟨⟨a, ha⟩, _⟩ := hx
    exact weakFreeRightPart_not_left hfree f hy a (heq.symm.trans ha)
  · exact weakFreePartition_target_no_cross_edge hfree f hx hy hedge'

/-- A Gaifman neighbour outside the root of an exclusive left source
vertex is again on the exclusive left, even for a noninjective map. -/
theorem weakFreePartition_left_step
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {x y : U}
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∉ weakFreeRootPart (sL := sL) (iL := iL) f)
    (hxy : GaifmanAdjacent Source.graph x y) :
    y ∈ weakFreeLeftPart (sL := sL) (iL := iL) f := by
  rcases weakFreePartition_covers hfree f y with hr | hl | hr
  · exact False.elim (hy hr)
  · exact hl
  · exact False.elim (weakFreePartition_source_no_cross_edge hfree f hf hx hr hxy)

/-- The analogous right-side edge saturation outside the root. -/
theorem weakFreePartition_right_step
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {x y : U}
    (hx : x ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    (hy : y ∉ weakFreeRootPart (sL := sL) (iL := iL) f)
    (hxy : GaifmanAdjacent Source.graph x y) :
    y ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f := by
  rcases weakFreePartition_covers hfree f y with hr | hl | hr
  · exact False.elim (hy hr)
  · exact False.elim
      (weakFreePartition_source_no_cross_edge hfree f hf hl hx hxy.symm)
  · exact hr

/-- Every Gaifman component after deleting the root preimage is
monochromatic with respect to the two exclusive target sides. -/
theorem weakFreePartition_component_left
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    (r : {x : U // x ∉ weakFreeRootPart (sL := sL) (iL := iL) f})
    (hr : r.1 ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    {y : U}
    (hy : y ∈ functionalComponentFrom Source
      (weakFreeRootPart (sL := sL) (iL := iL) f) r) :
    y ∈ weakFreeLeftPart (sL := sL) (iL := iL) f := by
  obtain ⟨hyRoot, hreach⟩ := hy
  have hprop :
      ∀ z : {x : U //
        x ∉ weakFreeRootPart (sL := sL) (iL := iL) f},
        Relation.ReflTransGen
          (outsideAdjacency Source.graph
            (weakFreeRootPart (sL := sL) (iL := iL) f)) r z →
        z.1 ∈ weakFreeLeftPart (sL := sL) (iL := iL) f := by
    intro z hz
    induction hz with
    | refl => exact hr
    | @tail a b hab hstep ih =>
        exact weakFreePartition_left_step hfree f hf ih b.2 hstep
  exact hprop ⟨y, hyRoot⟩ hreach

theorem weakFreePartition_component_right
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    (r : {x : U // x ∉ weakFreeRootPart (sL := sL) (iL := iL) f})
    (hr : r.1 ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f)
    {y : U}
    (hy : y ∈ functionalComponentFrom Source
      (weakFreeRootPart (sL := sL) (iL := iL) f) r) :
    y ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f := by
  obtain ⟨hyRoot, hreach⟩ := hy
  have hprop :
      ∀ z : {x : U //
        x ∉ weakFreeRootPart (sL := sL) (iL := iL) f},
        Relation.ReflTransGen
          (outsideAdjacency Source.graph
            (weakFreeRootPart (sL := sL) (iL := iL) f)) r z →
        z.1 ∈ weakFreeRightPart (sL := sL) (iL := iL) (iR := iR) f := by
    intro z hz
    induction hz with
    | refl => exact hr
    | @tail a b hab hstep ih =>
        exact weakFreePartition_right_step hfree f hf ih b.2 hstep
  exact hprop ⟨y, hyRoot⟩ hreach


/-- The exact common-root preimage separates EVERY left-exclusive
source vertex from EVERY right-exclusive source vertex by Gaifman
paths. This is the printed Section 3 observation prior to selecting
minimal separating cuts, and does not assume injectivity of the
homomorphism-embedding. -/
theorem weakFreePartition_root_separates_exclusive
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (f : U → W) (hf : Source.IsWeakHomomorphism Whole f)
    {x y : U}
    (hx : x ∈ weakFreeLeftPart (sL := sL) (iL := iL) f)
    (hy : y ∈ weakFreeRightPart
      (sL := sL) (iL := iL) (iR := iR) f) :
    ¬ ReachOutside Source.graph
      (weakFreeRootPart (sL := sL) (iL := iL) f)
      ⟨x, hx.2⟩ ⟨y, hy.2⟩ := by
  intro hpath
  have hyComponent :
      y ∈ functionalComponentFrom Source
        (weakFreeRootPart (sL := sL) (iL := iL) f)
        ⟨x, hx.2⟩ :=
    ⟨hy.2, hpath⟩
  have hyLeft : y ∈ weakFreeLeftPart
      (sL := sL) (iL := iL) f :=
    weakFreePartition_component_left hfree f hf
      ⟨x, hx.2⟩ hx hyComponent
  exact (Set.disjoint_left.mp
    (weakFreePartition_left_right_disjoint hfree f)) hyLeft hy

end AllThoseRamseyClasses.Lifts
