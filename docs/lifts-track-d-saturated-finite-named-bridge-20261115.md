# Track D — bridge from repaired saturation to finite-family folded strong AP

## Exact scope

For a small native language `L : Language` with finitely many old relation and function symbols, and a finite original-source vertex bound N, the type `BoundedSaturatedFinRepresentatives F N` is finite. Construct `boundedSaturationNamedFamily L F N` by treating EACH member (a complete source structure on `Fin n`, with its positive and negative native relations and complete function fibres) as one named forbidden source.

The theorem `avoidsBoundedSaturationNamed_iff_original`, subject to exact-head Lean CI, identifies the resulting native finite-named forbidden-free class **exactly** with `AvoidsGlobalFunctionalEHN F`, the unchanged original shadow class.

### Why this is not the old flawed quotient

For any saturated forbidden structure H on an arbitrary finite carrier, the previously constructed full-isomorphism cover supplies an index p and a **surjective FULL embedding** from the named representative p.source to H. Composing that embedding with a weak EHN witness H→Target produces a genuine weak EHN witness from one of the finite named representatives. Conversely, every named representative is itself saturated. This proves avoidance equivalence without identifying a source-generated weak quotient with an induced full substructure.

## Structural consequence and boundary

The independent module `FiniteFamilyMaximalTraceStrongAmalgamation.lean` ALREADY proves strong amalgamation of the alternative hereditary finite-named all-closed-component maximal-trace age for EVERY `FiniteNamedFunctionalSources`. It may therefore be instantiated with `boundedSaturationNamedFamily L F N`. The new theorem establishes that this alternative expansion projects to exactly the original native forbidden-free shadow.

The alternative folded language is NOT the original 2019 global minimal-separator canonical G-lift. In particular this bridge does not establish GlobalFunctionalPieceRegular G, the unrestricted printed Claim 2, or full Ramsey for the alternative lift. Also, JEP and any full reduct-surjectivity step must be checked in their existing finite-family APIs, not assumed from strong AP alone. The connectedness lemmas in this stacked PR allow JEP in positive-arity languages under source connectedness.

**Verification:** Newly written native Lean declarations and named axiom/active-root checks remain CI-pending. The numbered manuscript is frozen and collaborators' removed TODOs stay removed. The parent #1228 and stacked #1247 need independent full green exact-head CI before merging.

## Direct native integration of the old-language reduct

`boundedSaturationNamed_maximalTrace_exact_reduct` now specializes the previously established `finiteNamedMaximalTraceAge_exact_reduct` to the bounded saturated family. For EVERY finite old structure A, it asserts the exact equivalence: A avoids the ORIGINAL forbidden family iff it is the old-language shadow of a genuine member of the hereditary finite-named folded maximal-trace age. Together with the existing finite-named finite-fibre and strong-AP theorems, this is a direct alternative finite-family structural expansion, not just a naming-level reduction.

`boundedSaturationNamed_connectedNonempty` transfers original forbidden connectedness to ALL named saturated representatives. Under the existing positive-arity assumption, the finite-named JEP theorem consequently applies to these representatives. This supplies the JEP hypothesis independently of strong AP, without suppressing nullary compatibility issues.

Both new declarations are **CI pending**, with explicit named axiom checks. They do NOT prove the original global minimal-separator G-lift strong AP, do NOT finish Ramsey, and require the original uniform source-size and finite-signature hypotheses for this named-family packaging.

## Direct structural theorem package (pending Lean CI)

The module now exposes the complete bounded-case specializations of the existing, separately proved finite-named theorems:

* `boundedSaturationNamed_maximalTrace_exact_reduct`: a finite native A has a genuine hereditary folded maximal-trace expansion iff A avoids the original F, assuming original size bound N
* `boundedSaturationFoldedAge_fibre_finite`: every fixed finite old native structure has a finite type of expanded age members, retaining complete old partial/set-function fibres
* `boundedSaturationFoldedAge_fibre_nonempty_iff_original`: that finite fibre is nonempty iff the old structure avoids F
* `boundedSaturationFoldedAge_strongAmalgamation`: any two expanded age members over a full common expanded root have a genuine strong amalgam in the same age
* `boundedSaturationFoldedAge_jointEmbedding_positiveArity`: if the original forbidden sources are finite, nonempty, connected and the native language has positive arities, the same expanded age has full JEP

The theorem statements and proofs are an **implementation candidate**, not a confirmed kernel theorem until the exact-head CI run passes. These clauses complete the structural age/precompactness/strong-AP/JEP package for the **bounded finite-signature alternative folded lift**, not the original global minimal-separator quotient lift. The Ramsey theorem, existence/identification of the Fraïssé limit, and infinite regular-family generalization are not inferred here.

If nullary old relation/function symbols are permitted, JEP still requires explicit compatibility of full empty roots. No false unconditional nullary-JEP claim was added.
