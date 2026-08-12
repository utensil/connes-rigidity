# Sorry evaluation after the paper-alignment pass

This is a declaration-level audit against Zhou,
[arXiv:2608.02327](https://arxiv.org/html/2608.02327), at
`arc/connes-next-wins` commit `e2d22bd`. The OpenAI
[ten-proofs](https://github.com/openai/ten-proofs) snapshot
`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6` supplies reusable proof patterns
only.

## Inventory

The source scan finds one literal `sorry` in Lean:

| File | Declaration | Disposition |
| --- | --- | --- |
| `ComparatorChallenges/F_ConnesZhou.lean:265` | independent Comparator `theoremA` challenge | intentional external verification boundary |

There are no project `sorry` declarations, no project `axiom` declarations,
and no `admit` declarations. The words in legacy comments describing
external inputs are not declarations of axioms.

## What was corrected instead of papered over

- The active Theorem A path was moved from the identity-action scaffold to
  `Construction.PaperKernel`.
- The ICC target was replaced by a direct three-case theorem because the
  quotient `SL₃(R) × Sp₄(F₂)` is not ICC.
- The non-isomorphism target now models the quotient automorphism induced by a
  hypothetical group isomorphism. Its semisimplicity boundary is quantified
  over all such quotient twists.
- The factor target was tied to the algebraic fiber shear, then completed by
  formalizing Haar transport, dual-action conjugacy, generator closure, and
  the spatial implementation.

## Completion boundary

| Area | Compiled mathematics | External input |
| --- | --- | --- |
| §2 | Tensor carrier, coefficientwise retraction, square span, and both actions | none |
| §3 | Compact dual/Haar model, Fourier transport, shear conjugacy, spatial witness, and tracial equivalence | none |
| §4 | Scalar spectral measures, finite detection, quotient and finite-extension transfer | the cited EJZK theorem for `SL₃(𝔽₂[t])` |
| §5 | Infinite kernel orbits, finite-quotient displacement, and three-case ICC | none |
| §6 | Characteristic kernel, quotient twists, semisimplicity split, and cocycle obstruction | none |
| §7 | Concrete composition in `Connes.theoremA` | EJZK, passed as a theorem parameter |

This is the project's locked scenario A: the external theorem cited by Zhou is
supplied by the caller, and Zhou's own construction and proof are formalized.
No project axiom declaration is used to manufacture that input.

## Verification

The full build at `e2d22bd` passed:

```text
lake build Connes ComparatorChallenges
Build completed successfully (8759 jobs).
```

The final axiom audit reports exactly:

```text
Connes.theoremA depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The Comparator sandbox still needs its Linux `landrun`, `lean4export`, and
`nanoda` tools. The local build and source audit do not claim that sandbox
verification.
