import PartiteConstruction.Functional.FreeAmalgamReassociate

/-!
# Converse reassociation for an ACTUAL full native functional diagram

Assume the actual middle source is M +_S T, the extension is
Ext = T +_R P, and the actual outer source is already presented
as Out = M +_S Ext, with compatible FULL embeddings of the middle
source and the attached piece into Out.

Then Out is exactly (M +_S T) +_R P, preserving every complete
set-valued function fibre and relation tuple. This is the
converse of the existing `IsFreeAmalgam.reassociate_right`
under the same explicit compatibility of the participating maps.

Neither S subset R nor R subset S is required. The roots are
allowed to be incomparable; the common source diagrams remain
genuinely FULL, not graph-only or arbitrary weak-map diagrams.

The theorem is a native algebraic reassociation tool for attaching
all outer-root tests while changing an inner piece in Claim 2.
It does not construct the required test extension nor prove
the geometric boundary or full outer-piece profile by itself.
-/

namespace AllThoseRamseyClasses.Lifts

open StructuralRamsey
open StructuralRamsey.Structure

universe u v
variable {L : Language.{u}}

/-- Converse to native `IsFreeAmalgam.reassociate_right` when all
four actual full source embeddings and their overlap equations
have been supplied. All four full functional diagram fields are
checked, not inferred from Gaifman-graph connectivity. -/
theorem fullFunctionalFreeAmalgam_reassociate_right_reverse
    {S M T C R P E X : Type v}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R} {Piece : Structure L P}
    {Ext : Structure L E} {Out : Structure L X}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {jT : Structure.Embedding Tstr Ext}
    {jP : Structure.Embedding Piece Ext}
    {kMid : Structure.Embedding Mid Out}
    {kP : Structure.Embedding Piece Out}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (hExt : Structure.IsFreeAmalgam rT rP jT jP)
    (eExt : Structure.Embedding Ext Out)
    (heT : ∀ t : T, eExt (jT t) = kMid (iT t))
    (heP : ∀ p : P, eExt (jP p) = kP p)
    (hRe : Structure.IsFreeAmalgam
      sM (jT.comp sT) (kMid.comp iM) eExt) :
    Structure.IsFreeAmalgam (iT.comp rT) rP kMid kP := by
  classical
  refine {
    covers := ?_
    overlap := ?_
    rel_iff := ?_
    func_iff := ?_
  }
  · intro z
    rcases hRe.covers z with ⟨m, hm⟩ | ⟨e, he⟩
    · exact Or.inl ⟨iM m, hm⟩
    · rcases hExt.covers e with ⟨t, ht⟩ | ⟨p, hp⟩
      · refine Or.inl ⟨iT t, ?_⟩
        calc
          z = eExt e := he
          _ = eExt (jT t) := congrArg eExt ht
          _ = kMid (iT t) := heT t
      · refine Or.inr ⟨p, ?_⟩
        calc
          z = eExt e := he
          _ = eExt (jP p) := congrArg eExt hp
          _ = kP p := heP p
  · intro c p
    constructor
    · intro hcp
      rcases hMid.covers c with ⟨m, hm⟩ | ⟨t, ht⟩
      · have hmp : (kMid.comp iM) m = eExt (jP p) := by
          calc
            (kMid.comp iM) m = kMid (iM m) := rfl
            _ = kMid c := congrArg kMid hm.symm
            _ = kP p := hcp
            _ = eExt (jP p) := (heP p).symm
        obtain ⟨s, hms, hjs⟩ :=
          (hRe.overlap m (jP p)).mp hmp
        have hjtp : jT (sT s) = jP p := hjs.symm
        obtain ⟨r, hsr, hpr⟩ :=
          (hExt.overlap (sT s) p).mp hjtp
        refine ⟨r, ?_, hpr⟩
        calc
          c = iM m := hm
          _ = iM (sM s) := congrArg iM hms
          _ = iT (sT s) :=
            (hMid.overlap (sM s) (sT s)).mpr
              ⟨s, rfl, rfl⟩
          _ = iT (rT r) := congrArg iT hsr
          _ = (iT.comp rT) r := rfl
      · have hjtp : jT t = jP p := by
          apply eExt.injective
          calc
            eExt (jT t) = kMid (iT t) := heT t
            _ = kMid c := congrArg kMid ht.symm
            _ = kP p := hcp
            _ = eExt (jP p) := (heP p).symm
        obtain ⟨r, htr, hpr⟩ :=
          (hExt.overlap t p).mp hjtp
        refine ⟨r, ?_, hpr⟩
        calc
          c = iT t := ht
          _ = iT (rT r) := congrArg iT htr
          _ = (iT.comp rT) r := rfl
    · rintro ⟨r, hc, hp⟩
      calc
        kMid c = kMid (iT (rT r)) := congrArg kMid hc
        _ = eExt (jT (rT r)) := (heT (rT r)).symm
        _ = eExt (jP (rP r)) := congrArg eExt
          ((hExt.overlap (rT r) (rP r)).mpr ⟨r, rfl, rfl⟩)
        _ = kP (rP r) := heP (rP r)
        _ = kP p := congrArg kP hp.symm
  · intro Rel xs
    constructor
    · intro hxs
      rcases (hRe.rel_iff Rel xs).mp hxs with
        ⟨ms, hms, heq⟩ | ⟨es, hes, heq⟩
      · refine Or.inl ⟨iM ∘ ms,
          (iM.map_rel_iff Rel ms).mpr hms, ?_⟩
        calc
          xs = (kMid.comp iM) ∘ ms := heq
          _ = kMid ∘ (iM ∘ ms) := by funext k; rfl
      · rcases (hExt.rel_iff Rel es).mp hes with
          ⟨ts, hts, hte⟩ | ⟨ps, hps, hpe⟩
        · refine Or.inl ⟨iT ∘ ts,
            (iT.map_rel_iff Rel ts).mpr hts, ?_⟩
          calc
            xs = eExt ∘ es := heq
            _ = eExt ∘ (jT ∘ ts) :=
              congrArg (fun f => eExt ∘ f) hte
            _ = kMid ∘ (iT ∘ ts) := by
              funext k
              exact heT (ts k)
        · refine Or.inr ⟨ps, hps, ?_⟩
          calc
            xs = eExt ∘ es := heq
            _ = eExt ∘ (jP ∘ ps) :=
              congrArg (fun f => eExt ∘ f) hpe
            _ = kP ∘ ps := by
              funext k
              exact heP (ps k)
    · rintro (⟨cs, hcs, rfl⟩ | ⟨ps, hps, rfl⟩)
      · exact (kMid.map_rel_iff Rel cs).mpr hcs
      · exact (kP.map_rel_iff Rel ps).mpr hps
  · intro Fn args y
    constructor
    · intro hy
      rcases (hRe.func_iff Fn args y).mp hy with
        ⟨margs, mb, hmb, hmargs, hmy⟩ |
        ⟨eargs, eb, heb, heargs, hey⟩
      · have hMidMem :
            iM mb ∈ Mid.func Fn (iM ∘ margs) := by
          have hmem : iM mb ∈ imageSet iM (Mstr.func Fn margs) :=
            ⟨mb, hmb, rfl⟩
          rw [iM.map_func Fn margs] at hmem
          exact hmem
        refine Or.inl ⟨iM ∘ margs, iM mb, hMidMem, ?_, ?_⟩
        · calc
            args = (kMid.comp iM) ∘ margs := hmargs
            _ = kMid ∘ (iM ∘ margs) := by funext k; rfl
        · exact hmy
      · rcases (hExt.func_iff Fn eargs eb).mp heb with
          ⟨targs, tb, htb, htargs, hty⟩ |
          ⟨pargs, pb, hpb, hpargs, hpy⟩
        · have hMidMem :
              iT tb ∈ Mid.func Fn (iT ∘ targs) := by
            have hmem : iT tb ∈ imageSet iT (Tstr.func Fn targs) :=
              ⟨tb, htb, rfl⟩
            rw [iT.map_func Fn targs] at hmem
            exact hmem
          refine Or.inl ⟨iT ∘ targs, iT tb, hMidMem, ?_, ?_⟩
          · calc
              args = eExt ∘ eargs := heargs
              _ = eExt ∘ (jT ∘ targs) :=
                congrArg (fun f => eExt ∘ f) htargs
              _ = kMid ∘ (iT ∘ targs) := by
                funext k
                exact heT (targs k)
          · calc
              y = eExt eb := hey
              _ = eExt (jT tb) := congrArg eExt hty
              _ = kMid (iT tb) := heT tb
        · refine Or.inr ⟨pargs, pb, hpb, ?_, ?_⟩
          · calc
              args = eExt ∘ eargs := heargs
              _ = eExt ∘ (jP ∘ pargs) :=
                congrArg (fun f => eExt ∘ f) hpargs
              _ = kP ∘ pargs := by
                funext k
                exact heP (pargs k)
          · calc
              y = eExt eb := hey
              _ = eExt (jP pb) := congrArg eExt hpy
              _ = kP pb := heP pb
    · rintro (⟨cargs, cb, hcb, rfl, rfl⟩ |
              ⟨pargs, pb, hpb, rfl, rfl⟩)
      · have hmem : kMid cb ∈ imageSet kMid (Mid.func Fn cargs) :=
          ⟨cb, hcb, rfl⟩
        rw [kMid.map_func Fn cargs] at hmem
        exact hmem
      · have hmem : kP pb ∈ imageSet kP (Piece.func Fn pargs) :=
          ⟨pb, hpb, rfl⟩
        rw [kP.map_func Fn pargs] at hmem
        exact hmem


/-- A fully compatible nested native functional diagram can be
reassociated in BOTH directions, with neither separating root
required to contain the other. The statement includes the exact
functional source semantics, not a graph-encoding surrogate. -/
theorem fullFunctionalFreeAmalgam_reassociate_right_iff
    {S M T C R P E X : Type v}
    {Start : Structure L S}
    {Mstr : Structure L M} {Tstr : Structure L T}
    {Mid : Structure L C}
    {Root : Structure L R} {Piece : Structure L P}
    {Ext : Structure L E} {Out : Structure L X}
    {sM : Structure.Embedding Start Mstr}
    {sT : Structure.Embedding Start Tstr}
    {iM : Structure.Embedding Mstr Mid}
    {iT : Structure.Embedding Tstr Mid}
    {rT : Structure.Embedding Root Tstr}
    {rP : Structure.Embedding Root Piece}
    {jT : Structure.Embedding Tstr Ext}
    {jP : Structure.Embedding Piece Ext}
    {kMid : Structure.Embedding Mid Out}
    {kP : Structure.Embedding Piece Out}
    (hMid : Structure.IsFreeAmalgam sM sT iM iT)
    (hExt : Structure.IsFreeAmalgam rT rP jT jP)
    (eExt : Structure.Embedding Ext Out)
    (heT : ∀ t : T, eExt (jT t) = kMid (iT t))
    (heP : ∀ p : P, eExt (jP p) = kP p) :
    Structure.IsFreeAmalgam (iT.comp rT) rP kMid kP ↔
      Structure.IsFreeAmalgam
        sM (jT.comp sT) (kMid.comp iM) eExt := by
  constructor
  · intro hOut
    exact Structure.IsFreeAmalgam.reassociate_right
      hMid hExt hOut eExt heT heP
  · intro hRe
    exact fullFunctionalFreeAmalgam_reassociate_right_reverse
      hMid hExt eExt heT heP hRe

end AllThoseRamseyClasses.Lifts
