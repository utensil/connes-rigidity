# OpenAI proof-port map

The public OpenAI snapshot is a provenance archive, not a dependency. The
primary source is pinned at `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`; the
organized historical source is pinned at `66af838`. Tracked proofs come only
from those public revisions or from the local Zhou development.

The historical commit identifiers below are provenance anchors. The current
tree is organized by Zhou's sections under `Connes/Paper/Section3` through
`Section7`; it deliberately does not preserve the order or filenames of the
construction history.

## Transfer method

1. Locate a declaration in a pinned public revision.
2. Extract the whole declaration with `scripts/extract-openai-slice`.
3. Place it at the smallest Zhou or reusable-foundation boundary, changing
   only imports, namespaces, and recorded carrier/name adaptations.
4. Build the focused target, then the complete `Connes` target.
5. Classify it as `exact`, `adapted`, or `local`.

`exact` means the proof survived with only namespace/import changes;
`adapted` records carrier or local-name changes; `local` is a proof written
for this formalization and makes no provenance claim.

## Current declaration-level ledger

| Zhou area | Current project boundary | Public source block | Status |
| --- | --- | --- | --- |
| §2 characteristic-two and quadratic algebra | `Foundation/LinearAlgebra/BooleanPolynomial.lean`, `QuadraticCocycle.lean` | `ConnesRigidity.lean:15-23`; archive `ArithmeticCocycle.lean:16-243` | adapted/local; generic quadratic-support theorem now specialized by §4 |
| §2 arithmetic symplectic carriers | `Foundation/LinearAlgebra/ArithmeticSymplectic.lean` | archive `SymplecticData.lean:32-166` | adapted, provenance `93fc374` |
| §2 concrete action and tensor calculations | `Construction/PaperActions.lean`, `PaperActionInstances.lean`, `SquareSpan.lean` | action-homomorphism vocabulary near monolith lines 13894 and 14266 | adapted/local; concrete actions and square-span calculation |
| §3 L² reindexing and finite-index induction | `Porting/CoreTransfer.lean`, `Foundation/OperatorAlgebra/FiniteIndex.lean` | `ConnesRigidity.lean:99-157`, `295-655` | exact/adapted; the unitary bridge now uses Mathlib directly |
| §3 dual, Fourier, and Haar construction | `Paper/Section3/Dual*.lean`, `Fourier*.lean` | generic Pontryagin-dual and Fourier vocabulary | adapted/local; concrete compact dual and Haar transport |
| §3 crossed-product and group-factor bridge | `Paper/Section3/Crossed*.lean`, `Group*.lean`, `Factor*.lean` | generic spatial-transfer patterns | adapted/local; direct endpoint `PaperFactorClosure.paperGroupFactors_isomorphic` |
| §4 property-(T) vocabulary | `Porting/CoreTransfer.lean` | `ConnesRigidity.lean:252-285` | exact, base provenance `69c8004` |
| §4 split-extension invariant | `Foundation/GroupTheory/SplitAbelianExtension.lean` | `ConnesRigidity.lean:16258-16412` | adapted, provenance `77cc5f7` |
| §4 finite charts and detector | `Paper/Section4/FiniteCharts.lean`, `Chart*.lean`, `AChart*.lean` | finite-support coefficient infrastructure | adapted/local; uses the reusable Boolean-polynomial support theorem |
| §4 spectral completion | `Paper/Section4/Spectral*.lean` | property-(T) transfer and spectral-measure patterns | adapted/local; scalar measures and both finite certificates |
| §§4–5 special-linear facts | `Foundation/GroupTheory/SpecialLinear/{Basic,ElementaryGeneration,ICC}.lean`, `Paper/Section5/ICCOrbits.lean` | `ConnesRigidity.lean:10419-10560` | adapted/local; the carrier, §4 generation proof, and §5 conjugacy/ICC proof have separate dependencies |
| §5 split-extension ICC | `Paper/Section5/ICC.lean` | `ConnesRigidity.lean:31899-31958` and archive ICC patterns | exact/adapted/local; direct three-case concrete proof on Zhou's two actions |
| §6 finite cocycle obstruction | `Paper/Section6/Nonisomorphism.lean` | finite quadratic-cocycle coboundary obstruction | local/adapted; exhaustive finite proof and basis representation |
| §6 characteristic quotient and transport | `Paper/Section6/Characteristic*.lean`, `QuotientModuleTransport.lean` | characteristic-kernel and module-transport patterns | local/adapted; quotient-twist-safe certificate |
| §6 semisimplicity and non-isomorphism | `Paper/Section6/ModuleSemisimple*.lean`, `Nonisomorphism*.lean` | linear-equivalence and exact-extension patterns | local/adapted; uses Mathlib semisimplicity transport directly |
| §7 assembly | `Paper/Section7/TheoremACompletion.lean`, `Main.lean` | no statement-compatible source block | local; direct §§3–6 certificates and final theorem |

The reusable algebraic and operator-algebraic mechanisms remain under
`Connes/Foundation`. The Zhou-specific instantiations live only under
`Connes/Paper`, so the directory graph now reflects the paper's dependency
graph instead of the chronological port history.

## External theorem boundary

The sole mathematical input not constructed here is exactly the cited EJZK
property-(T) theorem for Zhou's elementary group. The formal boundary is
`PropertyT PaperPropertyT.elementaryGroup`. Section 4 proves
`elementarySubgroup_eq_top` and supplies `elementaryEquivSL3`, so the familiar
SL₃ statement is derived internally rather than assumed in place of EJZK.

The independent Comparator challenge uses this same elementary-subgroup
boundary. It remains an external comparison target, not part of the
`Connes.theoremA` dependency graph.

## Proof-debt ledger

There is one literal `sorry`, intentionally outside the project solution path:

| Project file | Declaration | Disposition |
| --- | --- | --- |
| `ComparatorChallenges/F_ConnesZhou.lean` | independent `theoremA` challenge | Comparator boundary; not imported by `Connes` |

The paper-facing source has no `sorry`, `admit`, or `axiom` declaration. See
`docs/SORRY_EVAL.md` for the exact boundary and `docs/STATEMENT_MAP.md` for the
paper-to-declaration correspondence.
