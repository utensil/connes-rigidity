# Provenance

This project formalizes the mathematical statement of:

- Shuoxing Zhou, “ICC property(T) groups without W*-superrigidity,”
  [arXiv:2608.02327](https://arxiv.org/abs/2608.02327), submitted 3 August
  2026.
- OpenAI, “Ten Advances in Mathematics and Theoretical Computer Science,”
  [openai/ten-proofs](https://github.com/openai/ten-proofs), including the
  public Connes formalization and its Comparator challenge.

The main OpenAI reference is pinned for provenance at commit
[`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`](https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6).
The organized public descendant used for two arithmetic proof transfers is
pinned at
[`66af8383b1dbc53e21ceefc917a503b9bd88df51`](https://github.com/deancureton/ten-proofs/tree/66af8383b1dbc53e21ceefc917a503b9bd88df51).
It descends from the primary revision and retains its Apache-2.0 license.

The authoritative code-transfer ledger is
[`docs/PORT_MAP.md`](PORT_MAP.md). It records each affected local declaration
block, public source block, adaptation class, and modification summary. The
project does not import either source repository at build time.

Modules containing transferred proof blocks carry source notes identifying
the source and the modifications made here. Independently written modules may
cite mathematical or architectural precedents without making a code-transfer
claim. These notes do not imply review, sponsorship, or endorsement.

The paper is cited as a mathematical source. This repository does not
redistribute the paper's PDF, TeX source, or prose. Only independently written
exposition, Lean declarations, properly attributed modified source blocks, and
short bibliographic references are included.
