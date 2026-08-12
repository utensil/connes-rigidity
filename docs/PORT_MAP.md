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

The current heavy-proof arc is `arc/connes-next-wins` at `e2d22bd`. Its source
commits are pushed individually so each Lean file has an auditable boundary.

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
| §2 actual tensor retraction and square span | `Connes/Construction/PaperActions.lean`, `Connes/Construction/SquareSpan.lean` | no complete compatible source block | local/adapted, construction commits through `b7e5ae9` |
| §3 L² reindexing and regular action | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:99-157` | exact, base `69c8004` |
| §3 unitary/linear isometry bridge | `Connes/Foundation/OperatorAlgebra/UnitaryEquiv.lean` | `ConnesRigidity.lean:304-348` | exact, `3771cb0` |
| §3 finite-index induction | `Connes/Foundation/OperatorAlgebra/FiniteIndex.lean` | `ConnesRigidity.lean:295-655` | exact, `574685f` |
| §3 projection normality | `Connes/Foundation/OperatorAlgebra/StarAlgEquiv.lean` | `ConnesRigidity.lean:30217-30246` | exact, `b743a492` |
| §3 factor witness laws | `Connes/Foundation/OperatorAlgebra/FactorEquiv.lean`, `TracialEquiv.lean` | `ConnesRigidity.lean:13650-13699` | exact/adapted, `15679ee`, `c51d3dd` |
| §3 trace, dual, Haar, and crossed-product closure | `Connes/Foundation/OperatorAlgebra/GroupFactor.lean`, `PaperGroupQuotient.lean`, `PaperFactorClosure.lean` | generic source vocabulary and spatial-transfer pattern | local/adapted; completed through `e2d22bd` |
| §4 property-(T) vocabulary | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:252-285` | exact, base `69c8004` |
| §4 property-(T) spectral completion | `Connes/PaperSpectralPropertyT.lean`, `Connes/Foundation/OperatorAlgebra/PaperSpectralFiniteDetection.lean` | property-(T) transfer and spectral-detector patterns | adapted/local; scalar measures and both finite certificates completed through `a40d8bc` |
| §5 conjugacy and special-linear orbits | `Connes/Foundation/GroupTheory/SpecialLinear.lean`, `Connes/PaperICCOrbits.lean` | `ConnesRigidity.lean:10419-10560` | adapted/local; elementary generation at `80b9c01`, concrete orbit data completed before `451359a` |
| §5 split-extension ICC | `Connes/Foundation/GroupTheory/SemidirectICC.lean` | `ConnesRigidity.lean:31899-31958` | exact/adapted, `6200953` |
| §5 split-extension conjugacy orbits | `Connes/Foundation/GroupTheory/CocycleExtensionICC.lean` | archive `ConnesRigidity/ICC.lean:13-300` | adapted, `6f8ab9a` |
| §5 ICC completion | `Connes/PaperICC.lean`, `Connes/PaperICCOrbits.lean`, `Connes/PaperConcreteCompletion.lean` | semidirect, split-quotient, and infinite-module-orbit patterns | adapted/local; direct three-case proof and concrete orbit certificates |
| §6 normalized extension algebra | `Connes/Foundation/GroupTheory/CocycleExtension.lean` | archive `ConnesRigidity/CocycleExtension.lean:25-290` | adapted, `3186a1e` |
| §6 characteristic-kernel obstruction | `Connes/Foundation/GroupTheory/CharacteristicKernel.lean` | archive `ConnesRigidity/CharacteristicKernel.lean:24-137` | adapted, `6643c43` |
| §6 group invariants and commensurability | `Connes/Foundation/GroupTheory/GroupInvariants.lean` | `ConnesRigidity.lean:13952-14028` | exact/adapted, `1f8f2f3` |
| §6 order-four obstruction | `Connes/Foundation/GroupTheory/OrderFour.lean` | `ConnesRigidity.lean:36636-36694` | exact/adapted, `e8308c7` |
| §2 construction action seam | `Connes/Construction/PaperActionInstances.lean` | monolith action-homomorphism vocabulary around `13894` and `14266` | adapted, `609686c`, `9bd4a36`; concrete action pair |
| §4 finite-support charts | `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | source finite-support coefficient infrastructure | local/adapted, `f63f121`; target hypothesis repaired before porting |
| §6 semisimplicity transport | `Connes/Foundation/LinearAlgebra/Semisimple.lean` | source linear-equivalence transport pattern | local/adapted, `7fcb228`; instantiated concretely by `PaperModuleSemisimple.lean` |
| §4 quadratic weight | `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | OpenAI four-point quadratic support cover | local/adapted, `3f5f59b`; proved on the local coefficient representation |
| §6 finite cocycle obstruction | `Connes/PaperNonisomorphism.lean` | finite quadratic-cocycle coboundary obstruction | local/adapted; exhaustive kernel-checked finite proof plus basis representation, finalized at `451359a` |
| §6 characteristic module and semisimplicity | `Connes/PaperNonisomorphismEmbedding.lean`, `Connes/PaperModuleSemisimple.lean`, `Connes/PaperConcreteCompletion.lean` | characteristic-kernel and module-transport patterns | local/adapted; concrete quotient-twist-safe non-isomorphism certificate |
| §6 reduced extension obstruction | `Connes/Nonisomorphism.lean` | exact-extension/non-splitting pattern | local, `7d85b48`; deliberately scoped to the reduced carrier |
| §6 legacy quotient normal obstruction | `Connes/Nonisomorphism.lean` | finite normal-subgroup consequences | local, `7035415`; retained as a countercheck and not imported by the final path |
| §4 split-extension invariant | `Connes/Foundation/GroupTheory/SplitAbelianExtension.lean` | `ConnesRigidity.lean:16258-16412` | adapted, `77cc5f7`; supplies the kernel/quotient invariant-vector spine |
| §4 legacy spectral detector wrapper | `Connes/PropertyT.lean` | property-(T) detector input boundary | local, `9def9b9`; superseded by the concrete `PaperSpectralFiniteDetection` path |
| §2 placeholder equivalence | `Connes/Construction.lean` | identity-action carrier reduction | local compatibility check; records the legacy groups' definitional equality and identity equivalence |
| §5 placeholder ICC obstruction | `Connes/ICC.lean` | central-kernel conjugacy calculation | local, `dc1e85d`; proves both default ICC targets false; parameterized targets are proved in `7acff53` |

The compatible source-backed declarations above are the covered set from the
correspondence audit. Zhou-specific facts that had no statement-compatible
source block were proved locally on the concrete carriers. In particular,
`sl3_eq_elementary`, the spectral certificates, ICC orbit data,
characteristic-module argument, and crossed-product spatial witness are no
longer skeleton boundaries.

## Current proof-debt ledger

There is one literal `sorry`, and it is intentionally outside the project
solution path:

| Project file | Declaration | Disposition |
| --- | --- | --- |
| `ComparatorChallenges/F_ConnesZhou.lean` | independent `theoremA` challenge | Comparator boundary; not imported by the proof modules |

The active paper-facing files contain no `sorry`, `admit`, or `axiom`
declarations. The concrete completion modules instantiate the former typed
boundaries. The only remaining parameter of `Connes.theoremA` is the EJZK
property-(T) result explicitly cited by Zhou; see `docs/SORRY_EVAL.md`.

The historical organized OpenAI tree is useful for dependency ordering, but it
contains thousands of generated certificate files. The port boundary keeps
those artifacts out of this repository and follows the Zhou section/file
split instead.
