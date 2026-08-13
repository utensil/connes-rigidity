# connes-rigidity

> [!WARNING]
> Highly experimental, early-stage research. Everything here is provisional: expect frequent changes and early-stage proofs.

Lean 4 formalization of Shuoxing Zhou's *ICC property(T) groups without
W*-superrigidity*, arXiv:2608.02327.

The paper-facing path constructs Zhou's two groups and proves the factor,
property-(T), ICC, and non-isomorphism arguments. As in the paper, the cited
EJZK theorem that `EL₃(𝔽₂[t])` has property (T) is an explicit hypothesis of
the final theorem. The project proves `EL₃(𝔽₂[t]) = SL₃(𝔽₂[t])` and transports
property (T) across that identification; all other certificates used by the
final assembly are constructed internally.

`Connes.theoremA` depends only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. The sole source-level `sorry` is
in the independent Comparator challenge, which restates the target without
being imported by the solution. Its EJZK hypothesis uses the same elementary
subgroup boundary as `Connes.theoremA`.

The project is standalone and mathlib-only. It does not import OpenAI's
`ten-proofs` repository. Modified proof blocks derived from its public
Apache-2.0 sources are identified in their file headers and in the
[provenance manifest](docs/PORT_MAP.md).

Current scope and architecture are summarized in the
[formalization status](docs/STATUS.md). The
[statement map](docs/STATEMENT_MAP.md) connects Zhou's sections to their Lean
endpoints, and [provenance](docs/PROVENANCE.md) records the mathematical and
code sources.

Build the Lean libraries with:

```sh
lake exe cache get
lake build Connes ComparatorChallenges
```

The paper source is [arXiv:2608.02327](https://arxiv.org/abs/2608.02327).
The public reference formalization is
[openai/ten-proofs](https://github.com/openai/ten-proofs). This project is
not affiliated with or endorsed by either the paper's author or OpenAI.

Licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE) and
[docs/LICENSING.md](docs/LICENSING.md).
