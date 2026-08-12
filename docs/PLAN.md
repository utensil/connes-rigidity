# Formalization plan

The active layout follows Zhou's sections and keeps reusable machinery under
`Connes/Foundation/`. The legacy files remain available for counterchecks but
are not imported by `Connes.Main`.

| Paper section | Active Lean area | Status |
| --- | --- | --- |
| §2 Construction | `Connes/Construction/PaperActions.lean`, `SquareSpan.lean`, `PaperActionInstances.lean` | Complete: actual `A`, `C`, `D`, retraction, square span, and both action homomorphisms. |
| §3 Factor isomorphism | `Connes/PaperFactorIsomorphism.lean`, `Foundation/OperatorAlgebra/PaperFactorClosure.lean` | Complete: compact dual coordinates, Haar transport, crossed-product Fourier model, fiber shear, spatial witness, and tracial factor equivalence. |
| §4 Property (T) | `Connes/PaperSpectralPropertyT.lean`, `Foundation/OperatorAlgebra/PaperSpectralFiniteDetection.lean` | Complete relative to the cited EJZK theorem: spectral measures, finite detectors, quotient identifications, and finite-extension transfer are constructed. |
| §5 ICC | `Connes/PaperICCOrbits.lean`, `Connes/PaperConcreteCompletion.lean` | Complete: kernel orbits, finite-quotient displacement, and the three-case ICC argument. |
| §6 Non-isomorphism | `Connes/PaperNonisomorphism*.lean`, `Connes/PaperModuleSemisimple.lean` | Complete: characteristic-kernel transport, quotient twists, semisimplicity split, and finite cocycle obstruction. |
| §7 Completion | `Connes/PaperTheoremACompletion.lean`, `Connes/Main.lean` | Complete under the explicit EJZK hypothesis. |

The scenario-A formalization is complete: EJZK is packaged as the external
result cited by Zhou, while every argument internal to Zhou's paper is proved.
Scenario B, a formalization of EJZK itself, is a separate upstream project and
is not part of this paper's proof.

The project does not adopt the small-PR `lgta`/`lgth` policy used by other
repositories. It still pins Lean, uses dedicated worktrees, records public
provenance, runs the source audit, and keeps the independent Comparator gate.
