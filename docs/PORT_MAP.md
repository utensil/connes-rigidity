# Public code provenance manifest

This is the authoritative ledger for modified Lean declaration blocks derived
from the two public Apache-2.0 `ten-proofs` revisions used by this project.
Neither repository is a build dependency.

- **Primary:**
  [`openai/ten-proofs@94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`](https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6),
  abbreviated `primary` below.
- **Organized descendant:**
  [`deancureton/ten-proofs@66af8383b1dbc53e21ceefc917a503b9bd88df51`](https://github.com/deancureton/ten-proofs/tree/66af8383b1dbc53e21ceefc917a503b9bd88df51),
  abbreviated `organized` below.

Every row is classified **adapted** because the local file differs from the
source. Adaptations include file extraction, imports, namespaces, universe or
carrier names, and changes needed by the current Mathlib API. A range such as
`first`–`last` names the inclusive local declaration block; intervening helper
declarations are covered. Local declarations outside a listed range make no
code-transfer claim.

## Declaration-block ledger

| Local file and declaration block | Public source block | Modification summary |
| --- | --- | --- |
| `Connes/Porting/CoreTransfer.lean`: `l2Reindex_apply`–`leftRegularUnitary_apply` | [`primary/ConnesRigidity.lean:138-157`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L138-L157) | Extracted into `Connes.OpenAIPort`; imports and namespace qualifications changed. |
| `Connes/Porting/CoreTransfer.lean`: `hasAlmostInvariantUnitVectors_comp`–`hasKazhdanPropertyT_iff_of_mulEquiv` | [`primary/ConnesRigidity.lean:252-285`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L252-L285) | Extracted into the local property-(T) vocabulary; namespace qualifications changed. |
| `Connes/Core.lean`: `CountableDiscreteGroup`–`TracialGroupFactorsIsomorphic` | [`primary/ConnesRigidity.lean:42-242`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L42-L242) | Extracted the minimal group, representation, regular-factor, and tracial-equivalence vocabulary; changed namespace, narrowed the interface, and replaced the local conjugacy-class carrier with Mathlib's `conjugatesOf`. |
| `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean`: `eq_one_of_ne_zero` | [`primary/ConnesRigidity.lean:18-23`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L18-L23) | Renamed the elementary `ZMod 2` helper and placed it in the local Boolean-polynomial namespace. The rest of the file is local. |
| `Connes/Foundation/LinearAlgebra/ArithmeticSymplectic.lean`: `SymplecticIndex`–`standardQuadraticForm_add` | [`organized/ConnesRigidity/SymplecticData.lean:32-166`](https://github.com/deancureton/ten-proofs/blob/66af8383b1dbc53e21ceefc917a503b9bd88df51/ConnesRigidity/SymplecticData.lean#L32-L166) | Isolated the arithmetic carriers; narrowed imports and namespace. |
| `Connes/Foundation/LinearAlgebra/QuadraticCocycle.lean`: `ModTwoSymplecticGroup`–`integralQuadraticCocycle_isCocycle` | [`organized/ConnesRigidity/ArithmeticCocycle.lean:16-243`](https://github.com/deancureton/ten-proofs/blob/66af8383b1dbc53e21ceefc917a503b9bd88df51/ConnesRigidity/ArithmeticCocycle.lean#L16-L243) | Isolated the finite and integral cocycle calculations; narrowed imports and namespace. |
| `Connes/Foundation/OperatorAlgebra/BinaryPontryaginDual.lean`: `pointwiseDualTopology`–`pointwisePontryaginDualEquiv_apply_character` | [`primary/ConnesRigidity.lean:10717-11155`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L10717-L11155) | Extracted the binary character-coordinate layer; renamed carriers and namespace. |
| `Connes/Foundation/OperatorAlgebra/CrossedProduct.lean`: `HaarProbabilityAction`–`crossedProductModel` | [`primary/ConnesRigidity.lean:13496-14516`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L13496-L14516) | Extracted the generic crossed-product Hilbert model; removed paper-specific instances and updated local vocabulary. |
| `Connes/Foundation/OperatorAlgebra/CrossedProductTransport.lean`: `crossedHaarHilbertEquiv`–`crossedHaarHilbertEquiv_group_conj` | [`primary/ConnesRigidity.lean:14519-14692`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L14519-L14692) | Split generic Haar transport into its own module; imports and namespace changed. |
| `Connes/Foundation/OperatorAlgebra/CrossedProductFactorTransport.lean`: `crossedHaarHilbertEquiv_multiplier_conj`–`crossedHaarHilbertEquiv_mem_algebra_iff` | [`primary/ConnesRigidity.lean:29950-30030`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L29950-L30030) | Split generator-closure transport into a reusable module; imports and namespace changed. |
| `Connes/Foundation/OperatorAlgebra/FiniteIndex.lean`: `CountableDiscreteGroup.subgroup`–`hasKazhdanPropertyT_subgroup_of_finiteIndex` | [`primary/ConnesRigidity.lean:295-655`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L295-L655) | Extracted finite-index induction; adapted namespace, imports, and local group vocabulary. |
| `Connes/Foundation/GroupTheory/SplitAbelianExtension.lean`: `SplitAbelianExtension`–`invariant_of_kernel_and_quotient` | [`primary/ConnesRigidity.lean:15961-16108`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L15961-L16108) | Extracted the generic extension interface and invariant-vector calculation; later spectral declarations were split out. |
| `Connes/Foundation/OperatorAlgebra/SpectralCriterion.lean`: `DiscreteCharacterSpace`–`spectral_criterion`; `continuous_character_evaluation`–`spectralEnergyTest_apply`; `continuous_dualCharacterAction` with its private helper | [`primary/ConnesRigidity.lean:16002-16173`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16002-L16173)<br>[`primary/ConnesRigidity.lean:16860-16867`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16860-L16867), [`16880-16893`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16880-L16893)<br>[`primary/ConnesRigidity.lean:18025-18036`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L18025-L18036) | Extracted the generic measure-to-invariant-vector spine; accepts local detector data. Moved the action and energy witnesses to their first consumer, kept the continuous-map constructor private, normalized the continuity theorem name, and added explicit measurable/integrable corollaries. |
| `Connes/Foundation/OperatorAlgebra/PositiveSpectralMeasure.lean`: `spectralUnitTest`–`spectralUnitTest_apply`; `PositiveSpectralFunctional`–`positiveVectorState_one`; `dualCharacterAction_mul`–`jointPositiveSpectralFunctional` | [`primary/ConnesRigidity.lean:16868-16878`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16868-L16878)<br>[`primary/ConnesRigidity.lean:16894-18024`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16894-L18024)<br>[`primary/ConnesRigidity.lean:18037-19073`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L18037-L19073) | Adapted the positive-functional, projection, and joint functional-calculus spine to local interfaces. The action and energy witnesses now live at their first consumer; later declarations in this file are local extensions. |
| `Connes/Foundation/OperatorAlgebra/NormalFixed.lean`: `normalFixedSubmodule`–`normalFixed_orthogonalResidual_displacement_le` | [`primary/ConnesRigidity.lean:20915-21166`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L20915-L21166) | Extracted normal-fixed and orthogonal representations; changed carrier names and namespace. |
| `Connes/Foundation/OperatorAlgebra/NormalizedHaar.lean`: `normalizedAddHaar`–`productHaar_preserving_addEquiv` | [`primary/ConnesRigidity.lean:12472-12581`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L12472-L12581) | Generalized the compact additive Haar lemmas from the paper carriers to arbitrary compact groups and updated simplification proofs. |
| `Connes/Foundation/OperatorAlgebra/Projection/ValuedSpectralMeasure.lean`: `ProjectionValuedSpectralMeasure`–`HasQuotientFixedApproximation` | [`primary/ConnesRigidity.lean:16191-16348`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L16191-L16348) | Extracted the projection-valued spectral interface, positive-atom argument, and quotient-approximation predicate; adapted namespace and local spectral interfaces. Later declarations are local extensions. |
| `Connes/Foundation/OperatorAlgebra/SpectralDetection.lean`: `measure_detection_gap_of_uniform_primitive_counts`–`probability_detection_gap_of_exhaustion` | [`primary/ConnesRigidity.lean:34332-34470`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L34332-L34470) | Extracted the measure-counting lemmas and made the paper-specific exhaustion an input. |
| `Connes/Foundation/OperatorAlgebra/SemidirectFubini.lean`: `l2CurryFiber`–`semidirectFubini_leftRegular_inr` | [`primary/ConnesRigidity.lean:34960-35158`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L34960-L35158) | Extracted the semidirect-product coordinate unitary; changed imports and namespace. |
| `Connes/Foundation/OperatorAlgebra/Projection/Supremum.lean`: `IsProjectionSupremum.map_starAlgEquiv`–`StarAlgEquiv.isNormal` | [`primary/ConnesRigidity.lean:35621-35749`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L35621-L35749) | Extracted the projection-supremum transport from the spatial witness, replaced the local multiplication relation by inherited operator order, and separated the abstract specification from its concrete proof. |
| `Connes/Foundation/OperatorAlgebra/FactorWitness.lean`: `SpatialWitness`–`SpatialWitness.toStarAlgEquiv`; `SpatialWitness.trace_preserving`–`tracialEquiv_of_spatialWitness` | [`primary/ConnesRigidity.lean:35621-35749`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L35621-L35749) | Renamed and generalized the spatial witness while preserving the spatial-to-tracial argument; projection-supremum transport now lives in the preceding module. |
| `Connes/Foundation/OperatorAlgebra/SemidirectClosure.lean`: `vonNeumannClosure_eq_of_factor_generators`–`semidirect_vonNeumannClosure_eq_inl_inr` | [`primary/ConnesRigidity.lean:35870-35940`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L35870-L35940) | Extracted the double-centralizer generator reduction; added a local conjugacy helper and changed namespace. |
| `Connes/Paper/Section3/FourierAction.lean`: `additiveLeftRegularUnitary_single`–`fourier_conjugates_regular_of_character_basis` | [`primary/ConnesRigidity.lean:31153-31229`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L31153-L31229) | Specialized the generic Fourier conjugacy block to Zhou's kernel and local Fourier unitary. |
| `Connes/Foundation/GroupTheory/SpecialLinear/ElementaryGeneration.lean`: `elementarySubgroup`–`elementarySubgroup_eq_top` | [`primary/ConnesRigidity.lean:30337-30825`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L30337-L30825) | Extracted the binary-polynomial row-reduction proof; adapted the index model, namespaces, and Mathlib APIs. |
| `Connes/Foundation/GroupTheory/SpecialLinear/ICC.lean`: `conjugates_eq_iff_quotient_commutes`–`specialLinear_transvection_injective` | [`primary/ConnesRigidity.lean:10240-10341`](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/ConnesRigidity.lean#L10240-L10341) | Extracted the generic transvection conjugacy lemmas; specialized the later ICC endpoint locally. |

## Independently written or reference-guided code

Files absent from the ledger make no code-transfer claim. This includes the
concrete Zhou carriers and actions under `Connes/Construction`, the paper
section endpoints under `Connes/Paper`, and reusable local results such as the
Boolean-polynomial support theorem and square-span abstraction. Those files
may cite a mathematical source or a public architectural precedent, but their
citations should not be read as a claim that a Lean declaration was copied.

## External theorem and proof-hole boundary

The sole substantive mathematical input not constructed here is the cited
EJZK property-(T) theorem for Zhou's elementary group. Its formal boundary is
`PropertyT PaperPropertyT.elementaryGroup`. The project proves the elementary
subgroup equality and transports this input to `SL₃` internally.

There is one literal `sorry`, in the independent
`ComparatorChallenges/F_ConnesZhou.lean` challenge. It is not imported by
`Connes`. The paper-facing source contains no `sorry`, `admit`, or project
`axiom` declaration.
