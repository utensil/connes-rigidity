# Formalization plan

The layout mirrors the six mathematical stages in arXiv:2608.02327 while
keeping reusable machinery under `Connes/Foundation/`.

| Paper section | Lean area | Skeleton status |
| --- | --- | --- |
| §2 Construction | `Connes/Construction.lean`, `Foundation/LinearAlgebra`, `Foundation/GroupTheory` | APIs and statement stubs |
| §3 Factor isomorphism | `Connes/FactorIsomorphism.lean`, `Foundation/OperatorAlgebra` | dual/shear/factor interfaces |
| §4 Property (T) | `Connes/PropertyT.lean` | EJZK is an explicit input field; heavy proofs are open |
| §5 ICC | `Connes/ICC.lean` | orbit and ICC statement stubs |
| §6 Non-isomorphism | `Connes/Nonisomorphism.lean` | characteristic-subgroup and module obstructions |
| §7 Completion | `Connes/Main.lean` | paper's four-assertion `theoremA` |

The first implementation target is compileable declaration structure, not
proof completion. The next slices should replace one focused cluster of
`sorry` bodies at a time and keep the Comparator challenge independent.

The project intentionally does not adopt small-PR `lgta`/`lgth` gates from
other formalization repositories. It still keeps the Lean toolchain pinned,
uses dedicated worktrees, records provenance, and retains the independent
Comparator design for the eventual headline theorem.
