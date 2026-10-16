import PartiteConstruction.Structure.FreeAmalgam

/-!
# Reparameterizing the root of a FULL functional free amalgam

A minimal separating cut may be described on its exact vertex-set
subtype, while the 2019 piece relation uses its ordered tuple
of roots, namely the standard finite carrier Fin n.

Replacing the root of an actual full functional free-amalgam
diagram by an ONTO FULL embedding into the old root leaves the
whole source, its two sides, relations and function incidences
unchanged. Its entire proof is a root-overlap transport;
all relation/function fields of the free-amalgam certificate
are inherited literally.

This is a reusable geometric normalization lemma and does NOT
turn an arbitrary weak rooted map into an embedding.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- An exact full functional free amalgam remains free when its
root is replaced by a fully isomorphic copy using an onto full
embedding. Only the parameterization of the overlap changes. -/
theorem freeAmalgam_precompose_root_onto
    {H H' E F W : Type v}
    {Root : Structure L H}
    {NewRoot : Structure L H'}
    {Left : Structure L E} {Right : Structure L F}
    {Whole : Structure L W}
    {sL : Structure.Embedding Root Left}
    {sR : Structure.Embedding Root Right}
    {iL : Structure.Embedding Left Whole}
    {iR : Structure.Embedding Right Whole}
    (hfree : Structure.IsFreeAmalgam sL sR iL iR)
    (k : Structure.Embedding NewRoot Root)
    (hk : Function.Surjective k) :
    Structure.IsFreeAmalgam (sL.comp k) (sR.comp k) iL iR := by
  refine {
    covers := hfree.covers
    overlap := ?_
    rel_iff := hfree.rel_iff
    func_iff := hfree.func_iff
  }
  intro a b
  constructor
  · intro hab
    obtain ⟨r, har, hbr⟩ := (hfree.overlap a b).mp hab
    obtain ⟨t, ht⟩ := hk r
    refine ⟨t, ?_, ?_⟩
    · calc
        a = sL r := har
        _ = sL (k t) := congrArg sL ht.symm
        _ = (sL.comp k) t := rfl
    · calc
        b = sR r := hbr
        _ = sR (k t) := congrArg sR ht.symm
        _ = (sR.comp k) t := rfl
  · rintro ⟨t, hat, hbt⟩
    apply (hfree.overlap a b).mpr
    exact ⟨k t, hat, hbt⟩

end AllThoseRamseyClasses.Lifts
