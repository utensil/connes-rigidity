# Statement map

The names below are the active paper-facing boundary. The legacy names are
kept only for compatibility checks. See [`TARGET_AUDIT.md`](TARGET_AUDIT.md)
and [`SORRY_EVAL.md`](SORRY_EVAL.md) for the faithfulness and proof-debt
assessment.

| Paper item | Lean declaration |
| --- | --- |
| §2 polynomial module | `Connes.Construction.PaperKernel.A` |
| §2 flip-fixed tensor module | `Connes.Construction.PaperKernel.C` |
| §2 diagonal/retraction | `Connes.Construction.PaperKernel.delta_diagonal`, `concreteRetractionData` |
| §2 square-span lemma | `Connes.Construction.PaperKernel.concreteSquareSpanData` |
| §2 first action | `Connes.Construction.PaperKernel.paperThetaOneHom` |
| §2 second action and quadratic correction | `Connes.Construction.PaperKernel.paperThetaTwoHom`, `thetaTwoLinearMap` |
| §2 groups | `Connes.Construction.PaperKernel.paperGammaOneOf`, `paperGammaTwoOf` |
| §3 quadratic dual map | `Connes.PaperFactorIsomorphism.quadraticMap`, `quadraticMap_diagonal` |
| §3 fiber shear | `Connes.PaperFactorIsomorphism.fiberShear`, `fiberShear_involutive` |
| §3 factor conclusion | `Connes.PaperFactorClosure.paperGroupFactors_isomorphic`, `Connes.PaperConcreteFactor.groupFactors_isomorphic` |
| §4 elementary generation | `Connes.SpecialLinear.sl3_eq_elementary` |
| §4 EJZK input | `Connes.PaperPropertyT.EJZKInput` |
| §4 spectral certificates | `Connes.PaperSpectralFiniteDetection.lambdaOneSpectralData`, `lambdaTwoSpectralData` |
| §4 property-(T) completion | `Connes.PaperSpectralPropertyT.completion_of_spectralData` |
| §5 ICC orbits and completion | `Connes.PaperICCOrbits.paperICCDataPair`, `Connes.PaperConcreteCompletion.paperGammaOne_icc`, `paperGammaTwo_icc` |
| §6 finite cocycle obstruction | `Connes.PaperNonisomorphism.FiniteCocycle.not_linearCoboundary` |
| §6 quotient modules | `Connes.PaperNonisomorphism.qRepresentationOne`, `qRepresentationTwoAlong` |
| §6 non-isomorphism | `Connes.PaperConcreteCompletion.paperGamma_not_isomorphic` |
| §7 Theorem A | `Connes.PaperTheoremACompletion.theoremA`, `Connes.theoremA` |

The Comparator challenge is an independent restatement of the headline and
does not import the solution modules. Its final theorem, like the project
theorem, takes the cited EJZK property-(T) result as an explicit hypothesis.
