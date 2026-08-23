# Mathematical target audit

> Internal mathematical correspondence review. It is not independent or peer
> review. For the status of this and other review angles, see
> [`AUDITS.md`](AUDITS.md); for the normative current architecture and trust
> boundary, see [`STATUS.md`](STATUS.md).

This audit compares the active declarations with Zhou,
[arXiv:2608.02327](https://arxiv.org/html/2608.02327). The public
[OpenAI ten-proofs](https://github.com/openai/ten-proofs) tree is a public code
source and architectural reference. Modified source blocks are identified in
[`PORT_MAP.md`](PORT_MAP.md); neither source repository is imported.

## Current result

The active paper-facing path uses the actual tensor kernel and the two Zhou
actions. It constructs every certificate required by §§2--6 and concludes
Theorem A from the EJZK property-(T) theorem for `EL₃(F₂[t])` cited in §4,
together with the internal proof that `EL₃ = SL₃`. The cited result is an
explicit theorem parameter, not a project axiom.

The retired identity-action compatibility path has been deleted. The only
exported construction path uses `Construction.PaperKernel` and the two
concrete Zhou actions.

## Section-by-section comparison

| Zhou section | Active Lean target | Assessment |
| --- | --- | --- |
| §2 | `Construction.PaperKernel.A`, `C`, `D`, `delta` | Faithful carrier model: `A` is `R^3`, `C` is the flip-fixed tensor submodule, and `D` is `(A ⊗ V*) × C`. The coefficientwise retraction, square-span certificate, and equivariance are compiled. |
| §2 | `PaperKernel.paperThetaOneHom`, `paperThetaTwoHom` | Faithful action formulas, including the finite quadratic correction in `thetaTwo`. The homomorphism and inverse laws are compiled. |
| §2 | `PaperKernel.paperGammaOne`, `paperGammaTwo` | Faithful concrete semidirect-product carriers, specialized from the reusable action-indexed `paperGammaOf` construction. |
| §3 | `PaperFactorIsomorphism.quadraticMap`, `fiberShear` | The algebraic dual coordinates, diagonal identity, and characteristic-two involution are proved. |
| §3 | `PaperFactorClosure.paperGroupFactors_isomorphic` | The raw compact dual, Haar probability action, crossed-product Fourier model, continuous character closure, fiber shear, spatial equivalence, vacuum transport, and trace-preserving factor equivalence are constructed. |
| §4 | `SpecialLinear.elementarySubgroup_eq_top`, `PaperPropertyT.elementaryEquivSL3`, `PaperSpectralFiniteDetection.lambdaOneSpectralData`, `lambdaTwoSpectralData` | The actual intermediate groups, scalar spectral measures, finite detectors, quotient identifications, and finite `Q` extension are constructed through one action-indexed extension spine. Only the cited EJZK property-(T) theorem for `EL₃` is a parameter; its transport to `SL₃` is internal. |
| §5 | `PaperICC.paper_actionData_one`, `paper_actionData_two`, `paper_gammaOne_icc`, `paper_gammaTwo_icc` | The actual `SL₃(R) × Sp₄(F₂)` quotient is used. Each action's kernel-orbit and finite-quotient displacement facts instantiate the direct three-case proof. |
| §6 | `PaperModuleSemisimpleTransport.paperGroups_not_isomorphic` | Characteristic-kernel transport, quotient representations definitionally attached to `paperThetaOneLinearHom` and `paperThetaTwoLinearHom`, arbitrary quotient twists, the semisimplicity split, and finite quadratic cocycle obstruction are constructed. |
| §7 | `Connes.theoremA` | The headline theorem takes exactly the cited EJZK result for `EL₃` and constructs the two concrete groups and all four conclusions. |

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
   target now fixes the actual two quotient representations, exposes that
   automorphism, and proves non-semisimplicity for every such twist; no
   generic conclusion-carrying `Data` remains.
4. The old factor target accepted an identity factor witness unrelated to the
   paper's shear. The factor conclusion now routes directly through the
   concrete Haar, dual-action, fiber-shear, generator-closure, and spatial
   implementation chain; no caller-supplied factor witness remains.

These corrections are discharged at the direct section endpoints and composed
by `PaperTheoremACompletion.theoremA`. No free data structure carrying a
Zhou-internal conclusion reaches the final theorem.

## Code-source correspondence

The modified declaration blocks derived from the public `ten-proofs` sources
are enumerated in [`PORT_MAP.md`](PORT_MAP.md). That manifest, rather than this
mathematical target comparison, controls code-transfer claims and modified-file
notices. The concrete Zhou endpoints are independently assembled against the
local carrier and analytic interfaces.

## Technical evidence

- Lean toolchain: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib revision: `c2d7843e04aa6cc44fa7e2b39422f24f7b725f00`
  (`master` as observed on 2026-08-23).
- Comparator tag: `v4.34.0-rc2`.
- lean4export tag: `v4.34.0-rc2`.
- Literal `sorry` declarations: one, in the independent Comparator
  `theoremA` challenge in `ComparatorChallenges/F_ConnesZhou.lean`.
- Project `axiom` and `admit` declarations: none.
- `#print axioms Connes.theoremA`: `propext`, `Classical.choice`, and
  `Quot.sound` only.
- Full local gate: `lake build Connes ComparatorChallenges`.
- Docstring gate: `scripts/check-paper-docstrings`.

These checks establish compilation, source inventory, and axiom closure. They
do not independently establish the mathematical fidelity assessed above; that
limitation and the planned follow-up are recorded in [`AUDITS.md`](AUDITS.md).
