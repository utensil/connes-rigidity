# Formalization status

The formalization of Zhou's Theorem A is complete relative to one explicit
external mathematical premise: the EJZK theorem that
`EL₃(𝔽₂[t])` has property (T). The project proves `EL₃ = SL₃`, transports the
premise across that identification, and constructs every other certificate
used by `Connes.theoremA`.

This document is the normative release-state summary. The public
[`AUDITS.md`](AUDITS.md) ledger separates automated verification, internal
review, independent review, and open semantic work. It also indexes the
detailed correspondence, proof-hole, provenance, and licensing records.

## Proof architecture

| Layer | Role | Canonical endpoint |
| --- | --- | --- |
| `Connes/Foundation` | Reusable algebra, group theory, harmonic analysis, and operator algebra | Imported by the section proofs, not assembled directly by users. |
| `Connes/Construction` | Zhou's concrete tensor kernel, retraction, acting group, and two actions | `PaperKernel.paperGammaOneOf`, `paperGammaTwoOf` |
| `Connes/Paper/Section3` | Compact dual, Haar/Fourier transport, fiber shear, and group-factor equivalence | `PaperFactorClosure.paperGroupFactors_isomorphic` |
| `Connes/Paper/Section4` | Elementary generation, spectral measures and detectors, and property-(T) transfer | `PaperSpectralPropertyT.completion_of_spectralData` |
| `Connes/Paper/Section5` | Concrete orbit calculations and the three-case ICC argument | `PaperICC.paper_gammaOne_icc`, `paper_gammaTwo_icc` |
| `Connes/Paper/Section6` | Characteristic-kernel transport, quotient twists, semisimplicity, and the cocycle obstruction | `PaperModuleSemisimpleTransport.paperGroups_not_isomorphic` |
| `Connes/Paper/Section7`, `Connes/Main.lean` | Proposition-valued assembly of §§3-6 | `Connes.theoremA` |

The paper-to-declaration correspondence is detailed in
[`STATEMENT_MAP.md`](STATEMENT_MAP.md). Public code-source attribution is kept
separately in [`PORT_MAP.md`](PORT_MAP.md).

## Trust and proof-hole boundary

- `Connes.theoremA` uses only Lean's standard `propext`, `Classical.choice`,
  and `Quot.sound` axioms.
- The solution path has no `sorry`, `admit`, or project `axiom` declaration.
- The one source-level `sorry` is the independent Comparator restatement. It
  is not imported by `Connes`.
- The Linux `landrun`/`lean4export`/`nanoda` Comparator sandbox is automated
  by `.github/workflows/comparator.yml`; a successful workflow run is the
  authoritative verification record.

## Reproducible local checks

```sh
lake exe cache get
lake build Connes ComparatorChallenges
scripts/check-paper-docstrings
```

The Comparator's stronger Linux command is documented in
[`COMPARATOR.md`](COMPARATOR.md).
