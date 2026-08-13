# Statement map

The names below are the active paper-facing boundary. See
[`STATUS.md`](STATUS.md) for the current architecture and trust boundary.

| Paper item | Lean declaration |
| --- | --- |
| §2 polynomial module | `Connes.Construction.PaperKernel.A` |
| §2 flip-fixed tensor module | `Connes.Construction.PaperKernel.C` |
| §2 diagonal/retraction | `Connes.Construction.PaperKernel.delta_diagonal`, `delta_surjective`, `delta_equivariant_of_squareSpanData` |
| §2 square-span lemma | `Connes.Construction.PaperKernel.concreteSquareSpanData` |
| §2 first action | `Connes.Construction.PaperKernel.paperThetaOneHom` |
| §2 second action and quadratic correction | `Connes.Construction.PaperKernel.paperThetaTwoHom`, `thetaTwoLinearMap` |
| §2 groups | `Connes.Construction.PaperKernel.paperGammaOneOf`, `paperGammaTwoOf` |
| §3 quadratic dual map | `Connes.PaperFactorIsomorphism.quadraticMap`, `quadraticMap_diagonal` |
| §3 fiber shear | `Connes.PaperFactorIsomorphism.fiberShear`, `fiberShear_involutive` |
| §3 factor conclusion | `Connes.PaperFactorClosure.paperGroupFactors_isomorphic` |
| §4 elementary generation and `EL₃ = SL₃` | `Connes.SpecialLinear.elementarySubgroup_eq_top`, `Connes.PaperPropertyT.elementaryEquivSL3` |
| §4 EJZK input on `EL₃` | `Connes.PaperPropertyT.elementaryGroup`, `EJZKInput`, `sl3_propertyT_from_EJZK` |
| §4 spectral certificates | `Connes.PaperSpectralFiniteDetection.lambdaOneSpectralData`, `lambdaTwoSpectralData` |
| §4 property-(T) completion | `Connes.PaperSpectralPropertyT.completion_of_spectralData` |
| §5 ICC orbits and completion | `Connes.PaperICC.paper_dataPair`, `Connes.PaperICC.paper_gammaOne_icc`, `paper_gammaTwo_icc` |
| §6 finite cocycle obstruction | `Connes.PaperNonisomorphism.FiniteCocycle.not_linearCoboundary` |
| §6 concrete quotient modules | `Connes.PaperNonisomorphism.qRepresentationOne`, `qRepresentationTwoAlong` |
| §6 non-isomorphism | `Connes.PaperModuleSemisimpleTransport.paperGroups_not_isomorphic` |
| §7 Theorem A | `Connes.PaperTheoremACompletion.theoremA`, `Connes.theoremA` |

The Comparator challenge is independent and does not import solution modules.
It states the same `EL₃` hypothesis and headline theorem as `Connes.theoremA`.
