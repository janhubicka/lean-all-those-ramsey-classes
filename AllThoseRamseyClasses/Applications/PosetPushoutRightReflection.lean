import AllThoseRamseyClasses.Applications.PosetRootedPushoutRelation

/-!
# Right-side induced reflection in the strong poset pushout

Root-factorized cross comparisons cannot create new comparisons
inside the right side. This proof carefully distinguishes points
in the induced common root (identified with their image in the
left side) from genuinely right-private points.

The result applies to arbitrary binary reflexive/transitive
relations whose restrictions to the common embedded root agree.
No root or side can silently acquire a new E-comparison.
Combined with `posetPushoutRelation_left_iff`, it gives the exact
two-sided induced reflection needed in the strong-amalgamation
application; global antisymmetry and the compatible vertex order
are independent remaining steps.
-/

namespace AllThoseRamseyClasses.Applications.OrderedPosets

open StructuralRamsey
open StructuralRamsey.RelStructure

private theorem poset_right_root_as_left
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (x : F) (hx : x ∈ Set.range sR) :
    ∃ d : H, sR d = x ∧
      FreeAmalgam.rightEmbedding Root Left Right sL sR x =
      FreeAmalgam.leftEmbedding Root Left Right sL sR (sL d) := by
  obtain ⟨d, hd⟩ := hx
  refine ⟨d, hd, ?_⟩
  calc
    FreeAmalgam.rightEmbedding Root Left Right sL sR x =
        FreeAmalgam.rightEmbedding Root Left Right sL sR (sR d) :=
          congrArg _ hd.symm
    _ = FreeAmalgam.leftEmbedding Root Left Right sL sR (sL d) :=
      (FreeAmalgam.left_right_overlap Root Left Right sL sR d).symm

private theorem poset_right_private_as_fresh
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (x : F) (hx : x ∉ Set.range sR) :
    FreeAmalgam.rightEmbedding Root Left Right sL sR x =
      Sum.inr ((), ⟨x, hx⟩) := by
  change Attachment.copyMap Right
      (FreeAmalgam.support Root Left Right sL sR)
      Left (fun _ : Unit =>
        FreeAmalgam.overlapEmbedding Root Left Right sL sR)
      () x = Sum.inr ((), ⟨x, hx⟩)
  exact Attachment.copyMap_not_mem () x hx

/-- A full induced root and two transitive side relations suffice
to reflect every right-side comparison. The cross comparisons are
required to factor through an actual root vertex. -/
theorem posetPushoutRelation_right_iff
    {H E F : Type}
    (Root : RelStructure Lang H)
    (Left : RelStructure Lang E)
    (Right : RelStructure Lang F)
    (sL : Embedding Root Left) (sR : Embedding Root Right)
    (pL : E → E → Prop) (pR : F → F → Prop)
    (hReflL : ∀ a : E, pL a a)
    (hTransR : ∀ a b c : F, pR a b → pR b c → pR a c)
    (hRoot : ∀ d e : H,
      pL (sL d) (sL e) ↔ pR (sR d) (sR e))
    (a b : F) :
    posetPushoutRelation Root Left Right sL sR pL pR
        (FreeAmalgam.rightEmbedding Root Left Right sL sR a)
        (FreeAmalgam.rightEmbedding Root Left Right sL sR b) ↔
      pR a b := by
  classical
  by_cases ha : a ∈ Set.range sR
  · by_cases hb : b ∈ Set.range sR
    · obtain ⟨da, hda, hma⟩ :=
        poset_right_root_as_left Root Left Right sL sR a ha
      obtain ⟨db, hdb, hmb⟩ :=
        poset_right_root_as_left Root Left Right sL sR b hb
      rw [hma, hmb]
      change pL (sL da) (sL db) ↔ pR a b
      rw [← hda, ← hdb]
      exact hRoot da db
    · obtain ⟨da, hda, hma⟩ :=
        poset_right_root_as_left Root Left Right sL sR a ha
      have hmb := poset_right_private_as_fresh
        Root Left Right sL sR b hb
      rw [hma, hmb]
      change (∃ d : H, pL (sL da) (sL d) ∧
        pR (sR d) b) ↔ pR a b
      constructor
      · rintro ⟨d, hdd, hdb⟩
        rw [← hda]
        exact hTransR (sR da) (sR d) b
          ((hRoot da d).mp hdd) hdb
      · intro hab
        exact ⟨da, hReflL (sL da), hda ▸ hab⟩
  · by_cases hb : b ∈ Set.range sR
    · obtain ⟨db, hdb, hmb⟩ :=
        poset_right_root_as_left Root Left Right sL sR b hb
      have hma := poset_right_private_as_fresh
        Root Left Right sL sR a ha
      rw [hma, hmb]
      change (∃ d : H, pR a (sR d) ∧
        pL (sL d) (sL db)) ↔ pR a b
      constructor
      · rintro ⟨d, had, hdd⟩
        rw [← hdb]
        exact hTransR a (sR d) (sR db)
          had ((hRoot d db).mp hdd)
      · intro hab
        exact ⟨db, hdb ▸ hab, hReflL (sL db)⟩
    · have hma := poset_right_private_as_fresh
        Root Left Right sL sR a ha
      have hmb := poset_right_private_as_fresh
        Root Left Right sL sR b hb
      rw [hma, hmb]
      rfl

end AllThoseRamseyClasses.Applications.OrderedPosets
