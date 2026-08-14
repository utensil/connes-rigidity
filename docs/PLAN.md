# Formalization status and architecture

> Historical planning record. For the concise normative release state, see
> [`STATUS.md`](STATUS.md).

The active layout follows Zhou's sections and keeps reusable machinery under
`Connes/Foundation/`. The retired identity-action and generic-witness
compatibility layers have been removed; `Connes.lean` now exposes only
`Connes.Main`.

| Paper section | Active Lean area | Status |
| --- | --- | --- |
| §2 Construction | `Connes/Construction/PaperActions.lean`, `SquareSpan.lean`, `PaperActionInstances.lean` | Complete: actual `A`, `C`, `D`, retraction, square span, and both action homomorphisms. |
| §3 Factor isomorphism | `Connes/Paper/Section3/FactorIsomorphism.lean`, `FactorClosure.lean` | Complete: compact dual coordinates, Haar transport, crossed-product Fourier model, fiber shear, spatial implementation, and direct closure through `PaperFactorClosure.paperGroupFactors_isomorphic`, with no caller-supplied spatial witness. |
| §4 Property (T) | `Connes/Paper/Section4/SpectralPropertyT.lean`, `SpectralFiniteDetection.lean` | Complete relative to the cited EJZK theorem for `EL₃`: `elementarySubgroup_eq_top` and `elementaryEquivSL3` transport it to `SL₃`; spectral measures, finite detectors, quotient identifications, and finite-extension transfer are internal. |
| §5 ICC | `Connes/Paper/Section5/ICCOrbits.lean` | Complete: kernel orbits, finite-quotient displacement, and the direct three-case ICC endpoints `PaperICC.paper_gammaOne_icc` and `paper_gammaTwo_icc`. |
| §6 Non-isomorphism | `Connes/Paper/Section6/Nonisomorphism*.lean`, `ModuleSemisimple*.lean` | Complete: the quotient representations are fixed to the concrete paper actions; characteristic-kernel transport, quotient twists, semisimplicity split, and finite cocycle obstruction are internal, ending at `PaperModuleSemisimpleTransport.paperGroups_not_isomorphic` with no generic conclusion wrapper. |
| §7 Completion | `Connes/Paper/Section7/TheoremACompletion.lean`, `Connes/Main.lean` | Complete under the explicit EJZK `EL₃(𝔽₂[t])` hypothesis. |

The formalization is complete relative to the cited EJZK input: EJZK is
packaged as the sole substantive external mathematical result cited by Zhou,
while every argument internal to Zhou's paper is proved. Formalizing EJZK
itself is outside the scope of this repository.

The reusable algebraic and operator-algebraic mechanisms live under
`Connes/Foundation/`; concrete carriers and actions live under
`Connes/Construction/`; Zhou's section endpoints live under `Connes/Paper/`;
and `Connes/Main.lean` assembles them. The project pins Lean, records public
provenance, and keeps the independent Comparator challenge outside the
solution dependency graph.
