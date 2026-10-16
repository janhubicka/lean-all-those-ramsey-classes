import AllThoseRamseyClasses.Applications.MetricCanonicalCutTransport
import AllThoseRamseyClasses.Applications.MetricCanonicalClassLastInLift
import AllThoseRamseyClasses.Applications.MetricCanonicalLiftEmbedding

/-!
# Ordered isometries induce order embeddings on canonical metric lifts

This finishes the *order-preservation component* of the finite canonical
S-metric closure construction. Class maxima need not commute with embeddings:
the robust invariant is the insertion cut on the embedded original vertices.

For two closure tags, increasing source anchors imply increasing target
anchors by the cut theorem. If source anchors coincide and levels increase,
the two target threshold classes overlap at the image of that original
anchor, and nested jump classes force weakly increasing target anchors.
The level then breaks a possible tie. No arbitrary representatives or
unsupported equality of class maxima are used.

This is not the class-level amalgamation, local completion or Ramsey proof.
-/

namespace AllThoseRamseyClasses.Applications.MetricSaturation

universe u v

/-- The cut at which a tag is inserted: an original is before a
new closure vertex precisely when it precedes the tag's last original. -/
theorem canonicalInsertion_old_lt_tag_iff {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (x : V) (tag : CanonicalJumpTag hpos hS hd) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inl x : V ⊕ CanonicalJumpTag hpos hS hd) < Sum.inr tag) ↔
    x ≤ canonicalClassLast hpos hS hd tag := by
  change toLex ((x, none) : V × WithBot ℝ) <
      toLex ((canonicalClassLast hpos hS hd tag,
        some (canonicalTagLevel tag)) : V × WithBot ℝ) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨heq, _⟩)
    · exact le_of_lt hlt
    · exact le_of_eq heq
  · intro hx
    rcases lt_or_eq_of_le hx with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      simpa only [WithBot.none_eq_bot, WithBot.some_eq_coe] using
        (WithBot.bot_lt_coe (canonicalTagLevel tag))

/-- Conversely, a closure tag is before an original exactly when
its last original anchor is strictly before that original. -/
theorem canonicalInsertion_tag_lt_old_iff {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (tag : CanonicalJumpTag hpos hS hd) (x : V) :
    (letI := canonicalInsertionLinearOrder hpos hS hd;
      (Sum.inr tag : V ⊕ CanonicalJumpTag hpos hS hd) < Sum.inl x) ↔
    canonicalClassLast hpos hS hd tag < x := by
  change toLex ((canonicalClassLast hpos hS hd tag,
        some (canonicalTagLevel tag)) : V × WithBot ℝ) <
      toLex ((x, none) : V × WithBot ℝ) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hlt | ⟨_, hbad⟩)
    · exact hlt
    · change WithBot.LT (some (canonicalTagLevel tag)) none at hbad
      cases hbad
  · intro hlt
    exact Or.inl hlt

/-- An exact isometry puts the image of a canonical tag's last source
original in the corresponding *target* jump class. This is membership,
not equality of the two last originals. -/
theorem mapCanonicalJumpTag_image_classLast_mem {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (tag : CanonicalJumpTag hpos hS hdV) :
    dW (f (canonicalClassLast hpos hS hdV tag))
      (canonicalTagRoot
        (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)) ≤
      canonicalTagLevel
        (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) := by
  let tgt := mapCanonicalJumpTag hpos hS hdV hdW f hf tag
  have hs := canonicalClassLast_class hpos hS hdV tag
  have hi := mapCanonicalJumpTag_class_mk hpos hS hdV hdW
    f hf tag (canonicalClassLast hpos hS hdV tag) hs
  have ht := canonicalTagRoot_class tgt
  have h := Quotient.exact (hi.trans ht.symm)
  change dW (f (canonicalClassLast hpos hS hdV tag))
    (canonicalTagRoot tgt) ≤ canonicalTagLevel tgt
  change dW (f (canonicalClassLast hpos hS hdV tag))
    (canonicalTagRoot tgt) ≤ tag.1.val at h
  rw [mapCanonicalJumpTag_level]
  exact h

/-- Two jump classes that contain a common original vertex are nested
whenever their threshold levels are comparable. Consequently the
last original of the lower class cannot lie after the last of the
higher class. No convex-order assumption is needed for this fact. -/
theorem canonicalClassLast_le_of_shared_member {S : Set ℝ}
    {V : Type u} [Finite V] [LinearOrder V]
    (hpos : Positive S) (hS : WellDefined S)
    {d : V → V → ℝ} (hd : MetricOn S d)
    (a b : CanonicalJumpTag hpos hS hd)
    (hle : canonicalTagLevel a ≤ canonicalTagLevel b)
    (x : V)
    (hxa : d x (canonicalTagRoot a) ≤ canonicalTagLevel a)
    (hxb : d x (canonicalTagRoot b) ≤ canonicalTagLevel b) :
    canonicalClassLast hpos hS hd a ≤
      canonicalClassLast hpos hS hd b := by
  have ha := canonicalClassLast_mem hpos hS hd a
  have hax : d (canonicalClassLast hpos hS hd a) x ≤
      canonicalTagLevel a :=
    metric_jump_threshold_trans hpos hS hd
      (Or.inr (canonicalTagLevel_jump a))
      (canonicalClassLast hpos hS hd a) (canonicalTagRoot a) x
      ha (by rw [hd.symm (canonicalTagRoot a) x]; exact hxa)
  have hab : d (canonicalClassLast hpos hS hd a)
      (canonicalTagRoot b) ≤ canonicalTagLevel b :=
    metric_jump_threshold_trans hpos hS hd
      (Or.inr (canonicalTagLevel_jump b))
      (canonicalClassLast hpos hS hd a) x (canonicalTagRoot b)
      (hax.trans hle) hxb
  exact canonicalClassLast_max hpos hS hd b
    (canonicalClassLast hpos hS hd a) hab

/-- Strictly increasing source anchors remain strictly increasing
in the target, although their *values* may not be preserved. -/
theorem mapCanonicalJumpTag_last_strict_of_last_strict {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (hconvW : JumpConvex S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hstrict : StrictMono f)
    (a b : CanonicalJumpTag hpos hS hdV)
    (hab : canonicalClassLast hpos hS hdV a <
      canonicalClassLast hpos hS hdV b) :
    canonicalClassLast hpos hS hdW
        (mapCanonicalJumpTag hpos hS hdV hdW f hf a) <
      canonicalClassLast hpos hS hdW
        (mapCanonicalJumpTag hpos hS hdV hdW f hf b) := by
  let m := canonicalClassLast hpos hS hdV b
  have hnot : ¬ f m ≤ canonicalClassLast hpos hS hdW
        (mapCanonicalJumpTag hpos hS hdV hdW f hf a) := by
    intro hle
    have hx := (canonicalClassLast_cut_iff_under_isometry
      hpos hS hdV hdW hconvW f hf hstrict a m).mpr hle
    exact (not_le_of_gt hab) hx
  have hleft : canonicalClassLast hpos hS hdW
      (mapCanonicalJumpTag hpos hS hdV hdW f hf a) < f m :=
    lt_of_not_ge hnot
  have hright : f m ≤ canonicalClassLast hpos hS hdW
      (mapCanonicalJumpTag hpos hS hdV hdW f hf b) :=
    (canonicalClassLast_cut_iff_under_isometry
      hpos hS hdV hdW hconvW f hf hstrict b m).mp (le_refl _)
  exact hleft.trans_le hright

/-- Full comparison of two *new* canonical closure vertices:
an ordered isometry preserves their lexicographic insertion order.
The common-anchor case uses nested jump classes, not a false
assumption that source and target class maxima are equal. -/
theorem canonicalInsertion_map_tags_strictMono {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (hconvW : JumpConvex S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hstrict : StrictMono f)
    (a b : CanonicalJumpTag hpos hS hdV)
    (hab : (letI := canonicalInsertionLinearOrder hpos hS hdV;
      (Sum.inr a : V ⊕ CanonicalJumpTag hpos hS hdV) < Sum.inr b)) :
    (letI := canonicalInsertionLinearOrder hpos hS hdW;
      (Sum.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf a) :
        W ⊕ CanonicalJumpTag hpos hS hdW) <
      Sum.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf b)) := by
  change toLex ((canonicalClassLast hpos hS hdV a,
      some (canonicalTagLevel a)) : V × WithBot ℝ) <
    toLex ((canonicalClassLast hpos hS hdV b,
      some (canonicalTagLevel b)) : V × WithBot ℝ) at hab
  rw [Prod.Lex.toLex_lt_toLex] at hab
  rcases hab with hlast | ⟨hsame, hlevelBot⟩
  · exact canonicalInsertion_tag_lt_tag_of_last_lt
      hpos hS hdW
      (mapCanonicalJumpTag hpos hS hdV hdW f hf a)
      (mapCanonicalJumpTag hpos hS hdV hdW f hf b)
      (mapCanonicalJumpTag_last_strict_of_last_strict
        hpos hS hdV hdW hconvW f hf hstrict a b hlast)
  · have hlevel : canonicalTagLevel a < canonicalTagLevel b := by
      simpa only [WithBot.some_eq_coe, WithBot.coe_lt_coe] using hlevelBot
    let aa := mapCanonicalJumpTag hpos hS hdV hdW f hf a
    let bb := mapCanonicalJumpTag hpos hS hdV hdW f hf b
    let x := canonicalClassLast hpos hS hdV a
    have hxa : dW (f x) (canonicalTagRoot aa) ≤
        canonicalTagLevel aa :=
      mapCanonicalJumpTag_image_classLast_mem hpos hS hdV hdW f hf a
    have hxb : dW (f x) (canonicalTagRoot bb) ≤
        canonicalTagLevel bb := by
      have h := mapCanonicalJumpTag_image_classLast_mem
        hpos hS hdV hdW f hf b
      change dW (f (canonicalClassLast hpos hS hdV a))
        (canonicalTagRoot
          (mapCanonicalJumpTag hpos hS hdV hdW f hf b)) ≤
        canonicalTagLevel
          (mapCanonicalJumpTag hpos hS hdV hdW f hf b)
      rw [hsame]
      exact h
    have hle : canonicalTagLevel aa ≤ canonicalTagLevel bb := by
      change canonicalTagLevel
        (mapCanonicalJumpTag hpos hS hdV hdW f hf a) ≤
        canonicalTagLevel
        (mapCanonicalJumpTag hpos hS hdV hdW f hf b)
      simpa only [mapCanonicalJumpTag_level] using (le_of_lt hlevel)
    have hanch : canonicalClassLast hpos hS hdW aa ≤
        canonicalClassLast hpos hS hdW bb :=
      canonicalClassLast_le_of_shared_member hpos hS hdW aa bb
        hle (f x) hxa hxb
    rcases lt_or_eq_of_le hanch with hlt | heq
    · exact canonicalInsertion_tag_lt_tag_of_last_lt
        hpos hS hdW aa bb hlt
    · apply canonicalInsertion_increasing_levels hpos hS hdW aa bb heq
      change canonicalTagLevel
          (mapCanonicalJumpTag hpos hS hdV hdW f hf a) <
        canonicalTagLevel
          (mapCanonicalJumpTag hpos hS hdV hdW f hf b)
      simpa only [mapCanonicalJumpTag_level] using hlevel

/-- The full canonical lift of an *ordered* isometry strictly preserves
the literal lexicographic insertion order on all old/new pairs.
Finiteness is needed for the class maxima, but S itself need not be finite. -/
theorem canonicalInsertion_mapCanonicalLift_strictMono {S : Set ℝ}
    {V : Type u} {W : Type v}
    [Finite V] [Finite W] [LinearOrder V] [LinearOrder W]
    (hpos : Positive S) (hS : WellDefined S)
    {dV : V → V → ℝ} (hdV : MetricOn S dV)
    {dW : W → W → ℝ} (hdW : MetricOn S dW)
    (hconvW : JumpConvex S dW)
    (f : V → W)
    (hf : ∀ x y : V, dW (f x) (f y) = dV x y)
    (hstrict : StrictMono f) :
    (letI := canonicalInsertionLinearOrder hpos hS hdV;
      letI := canonicalInsertionLinearOrder hpos hS hdW;
      StrictMono (mapCanonicalLift hpos hS hdV hdW f hf)) := by
  letI : LinearOrder (V ⊕ CanonicalJumpTag hpos hS hdV) :=
    canonicalInsertionLinearOrder hpos hS hdV
  letI : LinearOrder (W ⊕ CanonicalJumpTag hpos hS hdW) :=
    canonicalInsertionLinearOrder hpos hS hdW
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          have hab : a < b :=
            (canonicalInsertion_old_lt_iff hpos hS hdV a b).mp hxy
          change (Sum.inl (f a) :
            W ⊕ CanonicalJumpTag hpos hS hdW) <
            Sum.inl (f b)
          exact (canonicalInsertion_old_lt_iff hpos hS hdW (f a) (f b)).mpr
            (hstrict hab)
      | inr tag =>
          have ha : a ≤ canonicalClassLast hpos hS hdV tag :=
            (canonicalInsertion_old_lt_tag_iff hpos hS hdV a tag).mp hxy
          have haW := (canonicalClassLast_cut_iff_under_isometry
            hpos hS hdV hdW hconvW f hf hstrict tag a).mp ha
          change (Sum.inl (f a) :
            W ⊕ CanonicalJumpTag hpos hS hdW) <
            Sum.inr (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)
          exact (canonicalInsertion_old_lt_tag_iff hpos hS hdW
            (f a) (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)).mpr haW
  | inr tag =>
      cases y with
      | inl b =>
          have hb : canonicalClassLast hpos hS hdV tag < b :=
            (canonicalInsertion_tag_lt_old_iff hpos hS hdV tag b).mp hxy
          have hbW : canonicalClassLast hpos hS hdW
              (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) < f b := by
            have hn : ¬ b ≤ canonicalClassLast hpos hS hdV tag :=
              not_le_of_gt hb
            have hnW : ¬ f b ≤ canonicalClassLast hpos hS hdW
              (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) := by
              intro hle
              exact hn ((canonicalClassLast_cut_iff_under_isometry
                hpos hS hdV hdW hconvW f hf hstrict tag b).mpr hle)
            exact lt_of_not_ge hnW
          change (Sum.inr
              (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) :
              W ⊕ CanonicalJumpTag hpos hS hdW) < Sum.inl (f b)
          exact (canonicalInsertion_tag_lt_old_iff hpos hS hdW
            (mapCanonicalJumpTag hpos hS hdV hdW f hf tag)
            (f b)).mpr hbW
      | inr other =>
          change (Sum.inr
              (mapCanonicalJumpTag hpos hS hdV hdW f hf tag) :
              W ⊕ CanonicalJumpTag hpos hS hdW) <
            Sum.inr
              (mapCanonicalJumpTag hpos hS hdV hdW f hf other)
          exact canonicalInsertion_map_tags_strictMono
            hpos hS hdV hdW hconvW f hf hstrict tag other hxy

end AllThoseRamseyClasses.Applications.MetricSaturation
