# OpenAI proof-port map

The port arc treats the public OpenAI file as an archive of proof blocks, not
as a dependency. The source is the exact public snapshot
`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`; no local or private checkout is a
source for tracked files.

## Per-file method

1. Locate a declaration in the pinned public snapshot.
2. Extract its complete source block with
   `scripts/extract-openai-slice` into the review buffer.
3. Put the block in the smallest matching project file, changing only
   namespace, imports, and explicitly recorded name adaptations.
4. Build that file's target before moving to the next file.
5. Record whether the transfer is exact, adapted, or not applicable.

The extractor only prints a requested revision and line range. It never edits
the repository, and it does not accept a URL or an implicit current checkout.

## Current ledger

| Zhou area | Project file | OpenAI source block | Status |
| --- | --- | --- | --- |
| §3 factor vocabulary | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:137-157` | proof transfer with namespace adaptation |
| §4 property-(T) transfer | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:252-285` | proof transfer with namespace adaptation |
| §2 construction | `Connes/Construction.lean` | OpenAI tensor and action blocks | not type-compatible with the Zhou interface; retain skeleton boundary |
| §3 analytic shear | `Connes/FactorIsomorphism.lean` | OpenAI factor blocks | different group and dual data; port by later local slice |
| §4 detector argument | `Connes/PropertyT.lean` | OpenAI detector blocks | different external input boundary; port by later local slice |
| §5 ICC | `Connes/ICC.lean` | OpenAI conjugacy blocks | different group construction; port by later local slice |
| §6 nonisomorphism | `Connes/Nonisomorphism.lean` | OpenAI characteristic-subgroup blocks | different invariant; port by later local slice |

## Sorry target ledger

The transfer lane is declaration-level. Each row is compiled as its own Lean
file before it is considered for a skeleton `sorry`; a `not compatible` entry
means that the source declaration was not textually transplanted into a
different type.

| Project file | Current `sorry` targets | Transfer disposition |
| --- | --- | --- |
| `Connes/Construction.lean` | `delta_diagonal`, `thetaOne_is_action`, `thetaTwo_is_action` | not compatible; Zhou §2 data differs |
| `Connes/FactorIsomorphism.lean` | `fiberShear_involutive`, `fiberShear_preservesHaar`, `fiberShear_conjugates_actions`, `factorIsomorphism` | not compatible; Zhou §3 data differs |
| `Connes/PropertyT.lean` | `ejzkPropertyTInput`, `relative_propertyT_of_detector_bound`, `gammaOne_propertyT`, `gammaTwo_propertyT` | generic §4 vocabulary transferred; concrete targets remain open |
| `Connes/ICC.lean` | `sl3_infinite_orbits`, `module_infinite_orbits`, `gammaOne_icc`, `gammaTwo_icc` | not compatible; Zhou §5 group differs |
| `Connes/Nonisomorphism.lean` | `DTwo_not_semisimple`, `cocycle_not_coboundary`, `normal_module_characteristic`, `gammaOne_not_isomorphic_gammaTwo` | not compatible; Zhou §6 invariant differs |
| `Connes/Main.lean` | `theoremA` | composition target; port after section files |
| `Connes/Foundation/LinearAlgebra/*.lean` | `weight_lower_bound`, `coefficientChart_mono`, `coefficientCharts_cover`, `semisimple_invariant_under_linear_equiv`, `nonsplit_extension_not_semisimple`, `refinement_polarizes_to_form`, `cocycle_is_linear`, `cocycle_identity`, `sp4_transitive_on_nonzero` | local Zhou interfaces; no direct source block |
| `Connes/Foundation/GroupTheory/*.lean` | `transitive_on_nonzero_vectors`, `no_nontrivial_normal_elementary_abelian_subgroup`, `sl3_eq_elementary`, `sl3_isICC`, `no_nontrivial_abelian_normal_subgroup` | local Zhou interfaces; no direct source block |
| `Connes/Foundation/OperatorAlgebra/*.lean` | `tracialEquiv_of_spatialWitness`, `detector_bound_of_spectralInput`, `fiber_translation_preservesHaar`, `canonicalTrace_identity`, `dual_coordinates_exist`, `refl`, `symm`, `trans` | local Zhou interfaces; no direct source block |
| `ComparatorChallenges/F_ConnesZhou.lean` | `theoremA` | independent challenge statement; no solution transfer |

The historical organized OpenAI tree is useful for dependency ordering, but it
contains thousands of generated certificate files. The port boundary keeps
those artifacts out of this repository and follows the Zhou section/file
split instead.
