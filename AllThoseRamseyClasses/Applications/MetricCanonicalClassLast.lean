import AllThoseRamseyClasses.Applications.MetricCanonicalDistance

/-!
# The last original vertex in each finite metric jump class

The paper's canonical closure order inserts one representative
after the last original vertex in each proper-jump equivalence
class. In a finite linearly ordered S-metric, each such class is
nonempty, so it has a largest original member.

We record its membership and maximality, and show that a canonical
closure tag is uniquely determined by its positive jump level and
this last original vertex. That fact is useful for defining a
faithful lexicographic insertion key. It does not itself prove
the final order is convex nor preserve it under embeddings.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u

/-- Every positive-jump quotient class in a finite linearly ordered
original metric space has a greatest original member. -/
theorem exists_canonicalClassLast {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    ∃ m : V,
      d m (canonicalTagRoot tag) ≤ canonicalTagLevel tag ∧
      ∀ x : V,
        d x (canonicalTagRoot tag) ≤ canonicalTagLevel tag →
          x ≤ m := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let C : Finset V := Finset.univ.filter
    (fun x => d x (canonicalTagRoot tag) ≤ canonicalTagLevel tag)
  have hC : C.Nonempty := by
    refine ⟨canonicalTagRoot tag, ?_⟩
    have hle : 0 ≤ canonicalTagLevel tag :=
      (hpos (canonicalTagLevel tag) (canonicalTagLevel_jump tag).1).le
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hd.diag (canonicalTagRoot tag)]
    exact hle
  let m := C.max' hC
  have hm : d m (canonicalTagRoot tag) ≤ canonicalTagLevel tag := by
    have hmem : m ∈ C := Finset.max'_mem C hC
    exact (Finset.mem_filter.mp hmem).2
  refine ⟨m, hm, ?_⟩
  intro x hx
  apply Finset.le_max' C x
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩

/-- Choose the last original vertex in the class of a canonical tag;
the proof of existence is constructive up to Finset.max'. -/
noncomputable def canonicalClassLast {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) : V :=
  Classical.choose (exists_canonicalClassLast hpos hS hd tag)

/-- The last vertex belongs to the tag's original jump class. -/
theorem canonicalClassLast_mem {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    d (canonicalClassLast hpos hS hd tag) (canonicalTagRoot tag) ≤
      canonicalTagLevel tag :=
  (Classical.choose_spec (exists_canonicalClassLast hpos hS hd tag)).1

/-- Every original vertex of that jump class precedes its last
member in the given linear order. -/
theorem canonicalClassLast_max {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd)
    (x : V) (hx : d x (canonicalTagRoot tag) ≤ canonicalTagLevel tag) :
    x ≤ canonicalClassLast hpos hS hd tag :=
  (Classical.choose_spec (exists_canonicalClassLast hpos hS hd tag)).2 x hx

/-- The class containing its last original vertex is precisely
the quotient class encoded by the tag. -/
theorem canonicalClassLast_class {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) :
    Quotient.mk
      (jumpSetoid hpos hS hd tag.1.val (Or.inr tag.1.property))
      (canonicalClassLast hpos hS hd tag) = tag.2 := by
  have hmem := canonicalClassLast_mem hpos hS hd tag
  have hq : Quotient.mk
      (jumpSetoid hpos hS hd tag.1.val (Or.inr tag.1.property))
        (canonicalClassLast hpos hS hd tag) =
    Quotient.mk
      (jumpSetoid hpos hS hd tag.1.val (Or.inr tag.1.property))
        (canonicalTagRoot tag) := Quotient.sound hmem
  exact hq.trans (canonicalTagRoot_class tag)

/-- The pair (jump level, last original vertex) uniquely determines
the canonical (jump,class) tag, even if roots for the two tags
were chosen independently. -/
theorem canonicalTag_eq_of_level_last {S : Set ℝ} {V : Type u}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd)
    (hlevel : canonicalTagLevel a = canonicalTagLevel b)
    (hlast : canonicalClassLast hpos hS hd a =
      canonicalClassLast hpos hS hd b) : a = b := by
  rcases a with ⟨ja, qa⟩
  rcases b with ⟨jb, qb⟩
  have hj : ja = jb := Subtype.ext hlevel
  subst jb
  have ha := canonicalClassLast_class hpos hS hd (⟨ja, qa⟩ :
    CanonicalJumpTag hpos hS hd)
  have hb := canonicalClassLast_class hpos hS hd (⟨ja, qb⟩ :
    CanonicalJumpTag hpos hS hd)
  have hq : qa = qb := by
    calc
      qa = Quotient.mk
          (jumpSetoid hpos hS hd ja.val (Or.inr ja.property))
          (canonicalClassLast hpos hS hd (⟨ja, qa⟩ :
            CanonicalJumpTag hpos hS hd)) := ha.symm
      _ = Quotient.mk
          (jumpSetoid hpos hS hd ja.val (Or.inr ja.property))
          (canonicalClassLast hpos hS hd (⟨ja, qb⟩ :
            CanonicalJumpTag hpos hS hd)) := by rw [hlast]
      _ = qb := hb
  cases hq
  rfl

end AllThoseRamseyClasses.Applications.MetricSaturation
