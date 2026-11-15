import AllThoseRamseyClasses.Lifts.EHNFullTestBlockedSeamPalette

/-!
# Track D: genuine local test transport obstruction to source-changing collision repair

A source-changing repair in the original 2019 Section 3 proof
need not embed the entire old forbidden source FULLY into the
new source. Consequently the earlier full-embedding firewall
is too strong for the most interesting source-surgery cases.

The genuinely relevant weaker preservation condition is
TEST TRANSPORT: every old full native irreducible source test
must admit some full embedding in the new source with exactly
the prescribed new vertex images. The map Old → New may be
noninjective globally, and need NOT preserve arbitrary old
relations or whole native function fibres.

Under this condition every old blocked seam target value stays
blocked for the corresponding new source vertex, provided the
old source target map is preserved on the transported vertices.
The source-repair operation can remove a test-based collision
obstruction only by changing old target coordinates or by
failing to transport at least one old relevant irreducible test.

No quotient is silently identified with a full induced
substructure. No Claim 1/2, strong AP, or Ramsey conclusion.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u
variable {L : Language.{u}}

/-- Genuine transport of EVERY original full irreducible
source test to a replacement source with a specified vertex
map h : Old → New. NO global full embedding of Old into New
is assumed: h need only be a FULL map on every embedded test,
with each test transported through some actual full embedding.
This can be satisfied by a noninjective map on pairs that do
not occur in a common irreducible test. -/
def TransportsOriginalFullIrreducibleTests
    {V W : Type} (Old : Structure L V) (New : Structure L W)
    (h : V → W) : Prop :=
  ∀ {X : Type} (E : Structure L X),
    E.Irreducible →
    ∀ e : Structure.Embedding E Old,
      ∃ eNew : Structure.Embedding E New,
        ∀ x : X, eNew x = h (e x)

/-- Every genuine full native source embedding transports all
original full irreducible tests. This embeds the previously
validated full-extension firewall into the more general
test-transport interface, without identifying weak images
with full substructures. -/
theorem transportsOriginalFullIrreducibleTests_of_fullEmbedding
    {V W : Type}
    (Old : Structure L V) (New : Structure L W)
    (i : Structure.Embedding Old New) :
    TransportsOriginalFullIrreducibleTests Old New i := by
  intro X E _hIr e
  exact ⟨i.comp e, fun _ => rfl⟩

/-- Genuine transport of full irreducible source tests is
COMPOSITIONAL across successive SOURCE-CHANGING repairs,
even when neither whole source maps fully embeds globally.

Thus a finite sequence of test-preserving source replacements
cannot lose an old irreducible-test collision obstruction
unless some step fails the test-transport contract or
changes the original target coordinates. -/
theorem transportsOriginalFullIrreducibleTests_comp
    {V W Z : Type}
    (Old : Structure L V) (Middle : Structure L W)
    (New : Structure L Z)
    (h : V → W) (k : W → Z)
    (hTransport : TransportsOriginalFullIrreducibleTests Old Middle h)
    (kTransport : TransportsOriginalFullIrreducibleTests Middle New k) :
    TransportsOriginalFullIrreducibleTests Old New (k ∘ h) := by
  intro X E hIr e
  obtain ⟨eMid, hMid⟩ := hTransport E hIr e
  obtain ⟨eNew, hNew⟩ := kTransport E hIr eMid
  refine ⟨eNew, ?_⟩
  intro x
  calc
    eNew x = k (eMid x) := hNew x
    _ = k (h (e x)) := congrArg k (hMid x)
    _ = (k ∘ h) (e x) := rfl

/-- Genuine transport of an old full irreducible source test
forces the proposed Old→New coordinate map to separate its
distinct original vertices. This does NOT establish global
injectivity of h. -/
theorem transportedFullTest_pairwiseCoordinateInjection
    {V W : Type}
    (Old : Structure L V) (New : Structure L W)
    (h : V → W)
    (hTransport : TransportsOriginalFullIrreducibleTests Old New h)
    (a b : V) (hab : a ≠ b)
    (hTest : ∃ (X : Type) (E : Structure L X),
      E.Irreducible ∧
      ∃ e : Structure.Embedding E Old,
        ∃ x y : X, e x = a ∧ e y = b) :
    h a ≠ h b := by
  rintro hSame
  obtain ⟨X, E, hIr, e, x, y, hx, hy⟩ := hTest
  obtain ⟨eNew, heNew⟩ := hTransport E hIr e
  have hxNew : eNew x = h a := by
    calc
      eNew x = h (e x) := heNew x
      _ = h a := congrArg h hx
  have hyNew : eNew y = h b := by
    calc
      eNew y = h (e y) := heNew y
      _ = h b := congrArg h hy
  have hxy : x = y :=
    eNew.injective (hxNew.trans (hSame.trans hyNew.symm))
  exact hab (hx.symm.trans ((congrArg e.toFun hxy).trans hy))

/-- Every target value blocked by an actual irreducible test
in OLD remains blocked in NEW under test transport, even
when h : Old → New is NOT a full embedding of the whole old
source. The only target map premise is exact preservation of
old target coordinates on old vertices under h. -/
theorem testTransport_preserves_fullTestBlockedTargetImages
    {V W UT : Type}
    (Old : Structure L V) (New : Structure L W)
    (h : V → W)
    (hTransport : TransportsOriginalFullIrreducibleTests Old New h)
    (fOld : V → UT) (fNew : W → UT)
    (hTarget : ∀ v : V, fNew (h v) = fOld v)
    (a : V) :
    nativeFullTestBlockedTargetImages Old fOld a ⊆
      nativeFullTestBlockedTargetImages New fNew (h a) := by
  rintro d ⟨b, ⟨hab, X, E, hIr, e, x, y, hx, hy⟩, hD⟩
  obtain ⟨eNew, heNew⟩ := hTransport E hIr e
  have hNotEq : h a ≠ h b :=
    transportedFullTest_pairwiseCoordinateInjection
      Old New h hTransport a b hab
      ⟨X, E, hIr, e, x, y, hx, hy⟩
  have hxNew : eNew x = h a := (heNew x).trans (congrArg h hx)
  have hyNew : eNew y = h b := (heNew y).trans (congrArg h hy)
  exact ⟨h b, ⟨hNotEq, X, E, hIr, eNew,
    x, y, hxNew, hyNew⟩, (hTarget b).trans hD⟩

/-- Necessary source-surgery obstruction in contrapositive form.

If a target value d blocked by an original full irreducible
test of a becomes UNBLOCKED in the new source at h(a), while
all original old target coordinates are retained, then the
source-changing map h CANNOT transport all old full irreducible
tests to the new source.

This identifies a concrete failure of original test transport
that any genuine collision-removing source surgery must permit.
It is not an existence theorem for such surgery. -/
theorem unblockingOriginalTarget_forces_failure_of_fullTestTransport
    {V W UT : Type}
    (Old : Structure L V) (New : Structure L W)
    (h : V → W)
    (fOld : V → UT) (fNew : W → UT)
    (hTarget : ∀ v : V, fNew (h v) = fOld v)
    (a : V) (d : UT)
    (hOldBlocked : d ∈ nativeFullTestBlockedTargetImages Old fOld a)
    (hNewUnblocked : d ∉ nativeFullTestBlockedTargetImages New fNew (h a)) :
    ¬ TransportsOriginalFullIrreducibleTests Old New h := by
  intro hTransport
  exact hNewUnblocked
    (testTransport_preserves_fullTestBlockedTargetImages
      Old New h hTransport fOld fNew hTarget a hOldBlocked)

/-- ACTUAL source-test witness which must fail to survive
a collision-unblocking source surgery.

Suppose a target value d is blocked by the ORIGINAL source
pair a,b inside a genuine FULL irreducible source test E,
and d ceases to be blocked in the replacement New even though
old target coordinates are retained along h. Then one can
select the SAME old offending a,b and full E↪Old together
with a proof that NO full embedding E↪New has the specified
h-coordinate images. This is stronger than merely negating
global test transport: it produces the specific test that
any successful source surgery must destroy or modify.

There is no existence claim for such an unblocking surgery;
the obstruction is conditional on a genuine new source and
unblocked target. -/
theorem unblockingOriginalTarget_has_specific_untransportable_fullTest
    {V W UT : Type}
    (Old : Structure L V) (New : Structure L W)
    (h : V → W)
    (fOld : V → UT) (fNew : W → UT)
    (hTarget : ∀ v : V, fNew (h v) = fOld v)
    (a : V) (d : UT)
    (hOldBlocked : d ∈ nativeFullTestBlockedTargetImages Old fOld a)
    (hNewUnblocked : d ∉ nativeFullTestBlockedTargetImages New fNew (h a)) :
    ∃ b : V, a ≠ b ∧ fOld b = d ∧
      ∃ (X : Type) (E : Structure L X),
        E.Irreducible ∧
        ∃ (e : Structure.Embedding E Old) (x y : X),
          e x = a ∧ e y = b ∧
          ¬ ∃ eNew : Structure.Embedding E New,
            ∀ z : X, eNew z = h (e z) := by
  obtain ⟨b, ⟨hab, X, E, hIr, e, x, y, hx, hy⟩, hfb⟩ :=
    hOldBlocked
  refine ⟨b, hab, hfb, X, E, hIr, e, x, y, hx, hy, ?_⟩
  rintro ⟨eNew, heNew⟩
  have hxNew : eNew x = h a := (heNew x).trans (congrArg h hx)
  have hyNew : eNew y = h b := (heNew y).trans (congrArg h hy)
  have hNotEq : h a ≠ h b := by
    intro hSame
    have hxy : x = y :=
      eNew.injective (hxNew.trans (hSame.trans hyNew.symm))
    exact hab (hx.symm.trans ((congrArg e.toFun hxy).trans hy))
  exact hNewUnblocked
    ⟨h b, ⟨hNotEq, X, E, hIr, eNew,
      x, y, hxNew, hyNew⟩, (hTarget b).trans hfb⟩

/-- Even for a replacement source whose full old structure is
NOT retained, transporting all original irreducible tests
prevents one-vertex recolouring of h(a) to an originally
test-blocked d while retaining old target coordinates.

Unlike the earlier `fullNativeSourceExtension_blockedValue_prevents_EHN_recolor`,
the map h need not be a full native embedding of Old into New.
A successful repair must change more old target coordinates
or break the old irreducible test transport condition. -/
theorem testTransport_oldBlockedValue_prevents_newSourceOneVertexEHN
    {V W UT : Type} [DecidableEq W]
    (Old : Structure L V) (New : Structure L W)
    (Target : Structure L UT)
    (h : V → W)
    (hTransport : TransportsOriginalFullIrreducibleTests Old New h)
    (fOld : V → UT) (fNew : W → UT)
    (hTarget : ∀ v : V, fNew (h v) = fOld v)
    (a : V) (d : UT)
    (hBlocked : d ∈ nativeFullTestBlockedTargetImages Old fOld a) :
    ¬ New.IsEHNHomomorphismEmbedding Target
        (fun z : W => if z = h a then d else fNew z) := by
  intro hEHN
  have hNewBlocked :=
    testTransport_preserves_fullTestBlockedTargetImages
      Old New h hTransport fOld fNew hTarget a hBlocked
  exact (oneVertexRecolor_EHN_avoids_fullTestBlockedTargetImages
    New Target fNew (h a) d hEHN) hNewBlocked

end AllThoseRamseyClasses.Lifts
