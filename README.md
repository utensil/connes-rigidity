# connes-rigidity

> [!WARNING]
> Highly experimental research. Everything here is provisional: expect frequent changes and early-stage proofs.

Lean 4 formalization of Shuoxing Zhou's *ICC property(T) groups without
W*-superrigidity*, arXiv:2608.02327.

## Scope

The paper-facing path constructs Zhou's two groups and proves the factor,
property-(T), ICC, and non-isomorphism arguments. As in the paper, the cited
[EJZK theorem](https://arxiv.org/abs/1102.0031) that `EL₃(𝔽₂[t])` has
property (T) is an explicit hypothesis of the final theorem. The project proves
`EL₃(𝔽₂[t]) = SL₃(𝔽₂[t])` and transports property (T) across that
identification; all other certificates used by the final assembly are
constructed internally.

The project is standalone and mathlib-only. It does not import OpenAI's
`ten-proofs` repository. Modified proof blocks derived from its public
Apache-2.0 sources are identified in their file headers and in the
[provenance manifest](docs/PORT_MAP.md).

## Documentation

Current scope and architecture are summarized in the
[formalization status](docs/STATUS.md). The
[statement map](docs/STATEMENT_MAP.md) connects Zhou's sections to their Lean
endpoints, and [provenance](docs/PROVENANCE.md) records the mathematical and
code sources. See also the
[provisional formalization notes](https://utensil.github.io/forest/connes-0001/).

## Build

Build the Lean libraries with:

```sh
lake exe cache get
lake build Connes ComparatorChallenges
```

## Independent verification

`Connes.theoremA` depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. The solution path contains no
`sorry`; the sole source-level `sorry` is the theorem declaration in the
independent Mathlib-only
[Comparator challenge](ComparatorChallenges/F_ConnesZhou.lean), which is not
imported by the solution and carries the same explicit EJZK premise.

Linux CI rejects prebuilt project modules, builds the challenge and solution
under a self-tested Landlock filesystem sandbox with network isolation,
compares their elaborated statements and permitted axioms, and replays the
exported proof through both the Lean kernel and nanoda. See
[Comparator verification](docs/COMPARATOR.md) for the trust boundary and
reproducibility details.

## Sources and licensing

The paper source is [arXiv:2608.02327](https://arxiv.org/abs/2608.02327).
The public reference formalization is
[openai/ten-proofs](https://github.com/openai/ten-proofs). This project is
not affiliated with or endorsed by either the paper's author or OpenAI.

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) and
[docs/LICENSING.md](docs/LICENSING.md).
