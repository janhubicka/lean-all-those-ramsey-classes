# Track D — bridge from repaired saturation to finite-family folded strong AP

## Exact scope

For a small native language `L : Language` with finitely many old relation and function symbols, and a finite original-source vertex bound N, the type `BoundedSaturatedFinRepresentatives F N` is finite. Construct `boundedSaturationNamedFamily L F N` by treating EACH member (a complete source structure on `Fin n`, with its positive and negative native relations and complete function fibres) as one named forbidden source.

The new theorem `avoidsBoundedSaturationNamed_iff_original`, subject to exact-head Lean CI, identifies the resulting native finite-named forbidden-free class **exactly** with `AvoidsGlobalFunctionalEHN F`, the unchanged original shadow class.

### Why this is not the old flawed quotient

For any saturated forbidden structure H on an arbitrary finite carrier, the previously constructed full-isomorphism cover supplies an index p and a **surjective FULL embedding** from the named representative p.source to H. Composing that embedding with a weak EHN witness H→Target produces a genuine weak EHN witness from one of the finite named representatives. Conversely, every named representative is itself saturated. This proves avoidance equivalence without identifying a source-generated weak quotient with an induced full substructure.

## Structural consequence and boundary

The independent module `FiniteFamilyMaximalTraceStrongAmalgamation.lean` ALREADY proves strong amalgamation of the alternative hereditary finite-named all-closed-component maximal-trace age for EVERY `FiniteNamedFunctionalSources`. It may therefore be instantiated with `boundedSaturationNamedFamily L F N`. The new theorem establishes that this alternative expansion projects to exactly the original native forbidden-free shadow.

The alternative folded language is NOT the original 2019 global minimal-separator canonical G-lift. In particular this bridge does not establish GlobalFunctionalPieceRegular G, the unrestricted printed Claim 2, or full Ramsey for the alternative lift. Also, JEP and any full reduct-surjectivity step must be checked in their existing finite-family APIs, not assumed from strong AP alone. The connectedness lemmas in this stacked PR allow JEP in positive-arity languages under source connectedness.

**Verification:** Newly written native Lean declarations and named axiom/active-root checks remain CI-pending. The numbered manuscript is frozen and collaborators' removed TODOs stay removed. The parent #1228 and stacked #1247 need independent full green exact-head CI before merging.
