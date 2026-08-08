# Provenance

This project formalizes the mathematical statement of:

- Shuoxing Zhou, “ICC property(T) groups without W*-superrigidity,”
  [arXiv:2608.02327](https://arxiv.org/abs/2608.02327), submitted 3 August
  2026.
- OpenAI, “Ten Advances in Mathematics and Theoretical Computer Science,”
  [openai/ten-proofs](https://github.com/openai/ten-proofs), especially the
  public Connes formalization and its Comparator challenge.

The main OpenAI reference is pinned for provenance at commit
[`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`](https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6).
The organized historical source used by later proof transfers is pinned at
[`66af838`](https://github.com/openai/ten-proofs/tree/66af838). The reference
repository declares Apache-2.0. The project uses its public interfaces and
proof-organization patterns as reading material. The declaration-level port
lane copies only selected public proof blocks into small Zhou-oriented files
under `Connes/Porting/`, `Connes/Construction/`, and `Connes/Foundation/`;
their source spans and adaptations are recorded in
[`docs/PORT_MAP.md`](PORT_MAP.md). The project does not import
`ConnesRigidity.lean` or depend on the reference repository at build time.

Every module that follows a reference design carries a source note in its
header. Those notes identify the source and the modifications made here.
They do not imply review, sponsorship, or endorsement by OpenAI.

The paper is cited as a mathematical source. This repository does not
redistribute the paper's PDF, TeX source, prose, or private working notes.
Only independently written Lean declarations, selected public proof
fragments, and short bibliographic references are included.
