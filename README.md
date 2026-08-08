# connes-rigidity

Experimental Lean 4 skeleton for Shuoxing Zhou's *ICC property(T) groups
without W*-superrigidity*, arXiv:2608.02327.

This repository is a work in progress. The current branch lays out the
paper-shaped definitions, theorem statements, provenance records, and
independent Comparator challenge. Proof holes are intentional in this
skeleton; they are not claims of completed formalization.

The project is standalone and mathlib-only. It does not import OpenAI's
`ten-proofs` repository. Interfaces and proof-organization ideas that were
informed by that public reference are attributed in [docs/PROVENANCE.md](docs/PROVENANCE.md).

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
