# Licensing and attribution

The repository is distributed under the [Apache License, Version
2.0](../LICENSE).

## Sources

| Source | License/status | Use here |
| --- | --- | --- |
| [OpenAI `ten-proofs`](https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6) | Apache-2.0 | Primary public source for the modified declaration blocks listed in [`PORT_MAP.md`](PORT_MAP.md); no repository import. |
| [Organized `ten-proofs` descendant](https://github.com/deancureton/ten-proofs/tree/66af8383b1dbc53e21ceefc917a503b9bd88df51) | Apache-2.0 | Public descendant used for the two isolated arithmetic source files listed in [`PORT_MAP.md`](PORT_MAP.md). |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | Apache-2.0 | Sole Lake dependency. |
| [Zhou, arXiv:2608.02327](https://arxiv.org/abs/2608.02327) | arXiv non-exclusive distribution license for the submitted article | Mathematical source and citation. This repository does not copy the article text. |

Every modified file derived from either `ten-proofs` revision identifies its
source and states that it was changed. [`PORT_MAP.md`](PORT_MAP.md) is the
authoritative declaration-block ledger. Future code transfers must be added to
that ledger and to the affected file header, retain the Apache-2.0 license, and
carry a prominent modification notice as required by Apache-2.0 section 4(b).

Mathematical ideas, standard constructions, and independently written
interfaces are not labeled as code transfers. They may still be cited in
docstrings or in the provenance record when that helps readers locate the
mathematical source.

This project is not an OpenAI project and does not claim OpenAI endorsement.
The paper's author and arXiv are cited as sources, not as contributors to
this repository.

## Public traceability policy

Code-transfer claims in tracked files must resolve to a public repository,
full revision, source file, and declaration block. Bibliographic citations may
refer to publicly available papers without reproducing their prose or source.
