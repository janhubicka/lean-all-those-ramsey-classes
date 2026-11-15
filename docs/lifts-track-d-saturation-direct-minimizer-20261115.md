# Direct saturation full-image minimizer — proof simplification

The original repaired `exists_saturatedRelational_fullEmbeddingMinimizer` uses an intermediate injective EHN minimizer. That is sound but unnecessary in a relational language.

The new candidate theorem `exists_saturatedRelational_directFullSupportMinimizer` directly starts from a global source-support minimum over G=FullRangeEHNSaturation F and restricts it to the actual FULL induced target image. Because every relational subset is function-closed and G is closed under vertex-surjective EHN images, this new FULL induced image itself belongs to G. The support subtype of the full image is a *surjective image* of the original source support subtype; hence its finite cardinality cannot increase. Global minimality then makes the full image an equally minimal forbidden witness with a literal FULL target embedding.

This requires neither an EHN image to be injective nor an extra root-separating irreducible input cover. It avoids the extra injectivization/finite support bijection path entirely. Importantly it does NOT claim the original unsaturated family is closed under this operation or that arbitrary native function ranges are function-closed.

The theorem is a separate proof candidate on the stacked branch, allowing an adversarial direct-vs-two-step comparison before removing a redundant older proof. It has its own named axioms check and active proof-root. Full Lean CI on the exact current head is REQUIRED before marking it verified. Neither Claim 2 nor the unrestricted original canonical lift is proved.
