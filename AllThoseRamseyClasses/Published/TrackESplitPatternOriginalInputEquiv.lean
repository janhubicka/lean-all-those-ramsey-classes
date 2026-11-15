import AllThoseRamseyClasses.Published.TrackEHybridMaskSplitDomainCompatibility
import PartiteConstruction.Functional.OutputPartSingletonization

/-!
# Track E2: recover ORIGINAL primitive input equality patterns from split ones

The hybrid signature stores a singleton (F,q) symbol for each
original primitive function F and output part q. Its active
input roots are indexed by `FunctionInputPattern
(L.outputPartIndexed Parts)`, whereas the existing OLD
mask-domain/whole-output decoder and the new exact re-encoding
theorems are indexed by `FunctionInputPattern L`.

For a truly exact reconstruction one must not lose repeated
primitive argument positions or enlarge the distinct input
root when changing languages. This module constructs the
literal inverse pattern on the SAME root `Fin n` with the
SAME surjective argument map, using the original primitive
function symbol below `ULift`.

Splitting this recovered ORIGINAL pattern at the stored
part q recovers the original singleton-indexed input
pattern EXACTLY; conversely recovering the original
pattern after singleton-indexing by q is the identity.

The corresponding equalities of input-root sizes and
primitive input tuples are definitional, including repeated
primitive arguments and nullary function symbols. No
closure, extra vertices or functional decoding are used.

These two inverse identities are required to apply the
now-staged exact native split DOMAIN and POSITIVE incidence
theorems to ARBITRARY symbols of the entire split
patternGraph language, not just symbols already written as
`splitMaskInputAtPart p q`. The missing two-pass finite-
family sparse Ramsey theorem is not asserted here.
-/

namespace StructuralRamsey.Language

universe u v
variable {L : Language.{u}} {Parts : Type v}

/-- Recover the ORIGINAL F input equality pattern from a
singleton symbol (F,q), preserving the literal distinct
root and surjective primitive argument map. -/
def splitMaskOriginalInput
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    FunctionInputPattern L where
  symbol := p.symbol.1.down
  rootSize := p.rootSize
  argMap := p.argMap
  onto := p.onto

/-- Splitting the recovered original input equality pattern
at the STORED output part is literally inverse to recovery,
including all repeated primitive argument coordinates. -/
theorem splitMaskInputAtPart_original_eq
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    splitMaskInputAtPart (splitMaskOriginalInput p)
      p.symbol.2 = p := by
  cases p with
  | mk Fq m r hr =>
    cases Fq with
    | mk F q =>
      cases F with
      | up F =>
        rfl

/-- Recovering the original input equality pattern after
singleton indexing by q leaves the original pattern,
root size, and primitive argument map unchanged. -/
theorem splitMaskOriginalInput_atPart_eq
    (p : FunctionInputPattern L) (q : Parts) :
    splitMaskOriginalInput (splitMaskInputAtPart p q) = p := by
  cases p
  rfl

/-- The split pattern's primitive input vertex tuple is
exactly the ORIGINAL recovered pattern's primitive input
vertex tuple, on the SAME root map and carrier. -/
theorem splitMaskOriginalInput_argMap_eq
    (p : FunctionInputPattern (L.outputPartIndexed Parts)) :
    (splitMaskOriginalInput p).argMap = p.argMap := rfl

end StructuralRamsey.Language
