# Zhou target-faithfulness audit

This audit compares the active declarations with Zhou,
[arXiv:2608.02327](https://arxiv.org/html/2608.02327). The public
[OpenAI ten-proofs](https://github.com/openai/ten-proofs) tree is used only for
proof patterns and provenance. It is not imported.

## Result at `e2d22bd`

The active paper-facing path uses the actual tensor kernel and the two Zhou
actions. It constructs every certificate required by §§2--6 and concludes
Theorem A from the EJZK property-(T) theorem cited in §4. The cited result is
an explicit theorem parameter, not a project axiom.

The old identity-action path remains in compatibility files only. It is a
negative countercheck: its two groups are equal and isomorphic, so it cannot
be the theorem in the paper.

## Section-by-section comparison

| Zhou section | Active Lean target | Assessment |
| --- | --- | --- |
| §2 | `Construction.PaperKernel.A`, `C`, `D`, `delta` | Faithful carrier model: `A` is `R^3`, `C` is the flip-fixed tensor submodule, and `D` is `(A ⊗ V*) × C`. The coefficientwise retraction, square-span certificate, and equivariance are compiled. |
| §2 | `PaperKernel.paperThetaOneHom`, `paperThetaTwoHom` | Faithful action formulas, including the finite quadratic correction in `thetaTwo`. The homomorphism and inverse laws are compiled. |
| §2 | `PaperKernel.paperGammaOneOf`, `paperGammaTwoOf` | Faithful semidirect-product carriers parameterized by the concrete action pair. |
| §3 | `PaperFactorIsomorphism.quadraticMap`, `fiberShear` | The algebraic dual coordinates, diagonal identity, and characteristic-two involution are proved. |
| §3 | `PaperFactorClosure.paperGroupFactors_isomorphic` | The raw compact dual, Haar probability action, crossed-product Fourier model, continuous character closure, fiber shear, spatial equivalence, vacuum transport, and trace-preserving factor equivalence are constructed. |
| §4 | `PaperSpectralFiniteDetection.lambdaOneSpectralData`, `lambdaTwoSpectralData` | The actual intermediate groups, scalar spectral measures, finite detectors, quotient identifications, and finite `Q` extension are constructed. Only the cited EJZK property-(T) theorem is a parameter. |
| §5 | `PaperICCOrbits.paperICCDataPair` | The actual `SL₃(R) × Sp₄(F₂)` quotient is used. Kernel-orbit and finite-quotient displacement facts instantiate the direct three-case proof. |
| §6 | `PaperConcreteCompletion.paperGamma_not_isomorphic` | Characteristic-kernel transport, quotient representations under arbitrary quotient automorphisms, the semisimplicity split, and finite quadratic cocycle obstruction are constructed. |
| §7 | `Connes.theoremA` | The headline theorem takes exactly the cited EJZK result and constructs the two concrete groups and all four conclusions. |

The top-level `Construction.C`, `Construction.D`, `gammaOne`, and `gammaTwo`
are deliberately retained as legacy countercheck scaffolding. They are not
used by `Connes.Main`.

## Mathematical mismatch audit

The original targets had four material mismatches:

1. The default carriers were products with identity actions. That made the
   groups equal, killed the ICC claim through central kernel elements, and
   made non-isomorphism impossible.
2. The old ICC helper assumed the acting group was ICC. Zhou's acting group
   has a finite `Sp₄(F₂)` factor, so the paper proof needs the three cases for
   the quotient projection, pure kernel, and nontrivial finite quotient part.
3. The old non-isomorphism field accepted arbitrary propositions and a direct
   module equivalence. Zhou's argument first identifies a characteristic
   kernel and may twist the quotient action by an automorphism. The active
   target now exposes that automorphism and asks for non-semisimplicity for
   every such twist.
4. The old factor target accepted an identity factor witness unrelated to the
   paper's shear. The active file proves the shear algebra and names the
   measure, dual-action, and spatial implementation obligations explicitly.

These corrections are all discharged in the concrete completion modules. No
free data structure carrying a Zhou-internal conclusion reaches the final
theorem.

## OpenAI correspondence

Reusable transfers include the Boolean four-point support argument, finite
index and quotient property-(T) wrappers, semidirect conjugacy calculations,
finite cocycle obstruction, semisimplicity transport, and generic spatial to
tracial factor transfer. The OpenAI monolith and generated certificate tree
were not copied. No remaining active target has the same type as a complete
OpenAI theorem without local carrier and analytic adaptation.

## Current source audit

- Lean toolchain: `leanprover/lean4:v4.32.2`.
- Literal `sorry` declarations: one, the independent Comparator challenge at
  `ComparatorChallenges/F_ConnesZhou.lean:265`.
- Project `axiom` and `admit` declarations: none.
- `#print axioms Connes.theoremA`: `propext`, `Classical.choice`, and
  `Quot.sound` only.
- Full gate: `lake build Connes ComparatorChallenges`, 8759 jobs.
- No private paths, credentials, or private source material are tracked.
