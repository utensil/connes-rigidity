# OpenAI proof-port map

The port arc treats the public OpenAI files as archives of proof blocks, not
as dependencies. The main source is the exact public snapshot
`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`; the organized historical source
is pinned separately at `66af838`. No local or private checkout is a source
for tracked files.

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

## Current declaration-level ledger

Each compatible source block is split along the Zhou-oriented file boundary.
The listed files are standalone and are built before their commits are made.
`exact` means the proof term survived with only namespace/import changes;
`adapted` records a change of local names or carriers; `local` is a proof of a
Zhou skeleton declaration, not a claim that the OpenAI source proves it.

| Zhou area | Project file | OpenAI source block | Status |
| --- | --- | --- | --- |
| §2 characteristic-two scalars | `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | `ConnesRigidity.lean:15-23` | adapted, `c2c619c` |
| §2 symmetric quadratic data | `Connes/Construction/SymmetricTensor.lean` | `ConnesRigidity.lean:661-727` | adapted, `aa0b456` |
| §2 arithmetic symplectic carriers | `Connes/Foundation/LinearAlgebra/ArithmeticSymplectic.lean` | archive `ConnesRigidity/SymplecticData.lean:32-166` | adapted, `93fc374` |
| §2 finite and integral quadratic cocycles | `Connes/Foundation/LinearAlgebra/QuadraticCocycle.lean` | archive `ConnesRigidity/ArithmeticCocycle.lean:16-243` | adapted, `6ce74ea` |
| §2 shear obstructions | `Connes/Foundation/LinearAlgebra/SymplecticShear.lean` | archive `ConnesRigidity/ArithmeticCocycle.lean:246-402` | adapted, `5bb401f` |
| §2 retraction and refinement checks | `Connes/Construction.lean`, `Connes/Foundation/LinearAlgebra/Symplectic.lean` | no compatible source block | local, `ee6a907`, `cb6e39e` |
| §3 L² reindexing and regular action | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:99-157` | exact, base `69c8004` |
| §3 unitary/linear isometry bridge | `Connes/Foundation/OperatorAlgebra/UnitaryEquiv.lean` | `ConnesRigidity.lean:304-348` | exact, `3771cb0` |
| §3 finite-index induction | `Connes/Foundation/OperatorAlgebra/FiniteIndex.lean` | `ConnesRigidity.lean:295-655` | exact, `574685f` |
| §3 projection normality | `Connes/Foundation/OperatorAlgebra/StarAlgEquiv.lean` | `ConnesRigidity.lean:30217-30246` | exact, `b743a492` |
| §3 factor witness laws | `Connes/Foundation/OperatorAlgebra/FactorEquiv.lean`, `TracialEquiv.lean` | `ConnesRigidity.lean:13650-13699` | exact/adapted, `15679ee`, `c51d3dd` |
| §3 trace, dual, Haar, spectral boundaries | `Connes/Foundation/OperatorAlgebra/GroupFactor.lean`, `Fourier.lean`, `Haar.lean`, `Spectral.lean` | generic source vocabulary only | local closures, `b43a492`, `8b56cb5`, `5df6ecf`, `bf927cf` |
| §4 property-(T) vocabulary | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:252-285` | exact, base `69c8004` |
| §5 conjugacy and special-linear orbits | `Connes/Foundation/GroupTheory/SpecialLinear.lean` | `ConnesRigidity.lean:10419-10560` | adapted, `6764db2` |
| §5 split-extension ICC | `Connes/Foundation/GroupTheory/SemidirectICC.lean` | `ConnesRigidity.lean:31899-31958` | exact/adapted, `6200953` |
| §5 split-extension conjugacy orbits | `Connes/Foundation/GroupTheory/CocycleExtensionICC.lean` | archive `ConnesRigidity/ICC.lean:13-300` | adapted, `6f8ab9a` |
| §6 normalized extension algebra | `Connes/Foundation/GroupTheory/CocycleExtension.lean` | archive `ConnesRigidity/CocycleExtension.lean:25-290` | adapted, `3186a1e` |
| §6 characteristic-kernel obstruction | `Connes/Foundation/GroupTheory/CharacteristicKernel.lean` | archive `ConnesRigidity/CharacteristicKernel.lean:24-137` | adapted, `6643c43` |
| §6 group invariants and commensurability | `Connes/Foundation/GroupTheory/GroupInvariants.lean` | `ConnesRigidity.lean:13952-14028` | exact/adapted, `1f8f2f3` |
| §6 order-four obstruction | `Connes/Foundation/GroupTheory/OrderFour.lean` | `ConnesRigidity.lean:36636-36694` | exact/adapted, `e8308c7` |

The compatible source-backed declarations above are the covered set from the
correspondence audit. The reopened audit also closed the missed
`sl3_eq_elementary` boundary in `SpecialLinear.lean` at `c824b80`: its current
`ElementaryGeneration` definition is membership in `⊤`. The rest of the Zhou
theorem is kept as an explicit skeleton boundary rather than filled with
unrelated source code.

## Remaining sorry target ledger

The proof arc began with 29 `sorry` occurrences. There are now 19 in the
checked-out tree, including one in the independent Comparator challenge. Ten
project sites were closed per the evaluation in `docs/SORRY_EVAL.md`. The
following 18 project declarations remain Zhou-specific, opaque boundaries, or
otherwise type-incompatible:

| Project file | Current targets | Disposition |
| --- | --- | --- |
| `Connes/Construction.lean` | — | both current placeholder action laws closed in `eeb1a90`; real actions remain absent |
| `Connes/FactorIsomorphism.lean` | `fiberShear_preservesHaar`, `fiberShear_conjugates_actions` | Zhou §3 analytic construction; `factorIsomorphism` has an identity-witness scaffold closure in `2c0dbd2` |
| `Connes/PropertyT.lean` | `ejzkPropertyTInput`, `relative_propertyT_of_detector_bound`, `gammaOne_propertyT`, `gammaTwo_propertyT` | external input and concrete §4 transfer |
| `Connes/ICC.lean` | `sl3_infinite_orbits`, `module_infinite_orbits`, `gammaOne_icc`, `gammaTwo_icc` | Zhou §5 group construction |
| `Connes/Nonisomorphism.lean` | `DTwo_not_semisimple`, `cocycle_not_coboundary`, `normal_module_characteristic`, `gammaOne_not_isomorphic_gammaTwo` | Zhou §6 invariant |
| `Connes/Main.lean` | `theoremA` | §7 composition |
| `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | `weight_lower_bound`, `coefficientCharts_cover` | Zhou §4 polynomial argument |
| `Connes/Foundation/LinearAlgebra/Semisimple.lean` | `nonsplit_extension_not_semisimple` | Zhou §6 extension obstruction |
| `Connes/Foundation/LinearAlgebra/Symplectic.lean` | — | three current symplectic sites closed in `9725a15`; real `Sp₄(F₂)` action API remains |
| `Connes/Foundation/GroupTheory/Sp4.lean` | — | finite normal-abelian obstruction closed in `fcefc7f` |
| `Connes/Foundation/GroupTheory/SpecialLinear.lean` | — | full SL₃ ICC closed in `09206f0`; finite-normal consequence closed in `f25c252`; full §6 infinite result remains design work |
| `Connes/Foundation/OperatorAlgebra/FactorWitness.lean` | — | generic spatial-to-tracial transfer closed in `c933e72`; constructing the witness remains open |
| `ComparatorChallenges/F_ConnesZhou.lean` | challenge `theoremA` | independent comparator statement |

The historical organized OpenAI tree is useful for dependency ordering, but it
contains thousands of generated certificate files. The port boundary keeps
those artifacts out of this repository and follows the Zhou section/file
split instead. The reopened audit found no further source proof whose theorem
type matches one of the remaining project boundaries.
