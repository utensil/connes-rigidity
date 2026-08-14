# Proof-hole and axiom audit

> Internal source and trust-boundary review. For the status and limitations of
> this check, see [`AUDITS.md`](AUDITS.md). The normative current boundary is
> summarized in [`STATUS.md`](STATUS.md).

This is the current declaration-level boundary against Zhou,
[arXiv:2608.02327](https://arxiv.org/html/2608.02327), at
the repository's `main` result. Code provenance is recorded separately in
[`PORT_MAP.md`](PORT_MAP.md).

## Inventory

The source scan finds one literal `sorry` in Lean:

| File | Declaration | Disposition |
| --- | --- | --- |
| `ComparatorChallenges/F_ConnesZhou.lean` | independent Comparator `theoremA` challenge | intentional external verification boundary |

No solution module contains a `sorry`, `axiom`, or `admit` declaration.

The mathematical target corrections that removed the identity-action,
generic ICC, arbitrary non-isomorphism, and caller-supplied factor-witness
scaffolds are consolidated in [`TARGET_AUDIT.md`](TARGET_AUDIT.md).

## Completion boundary

| Area | Compiled mathematics | External input |
| --- | --- | --- |
| §2 | Tensor carrier, coefficientwise retraction, square span, and both actions | none |
| §3 | Compact dual/Haar model, Fourier transport, shear conjugacy, spatial witness, and tracial equivalence | none |
| §4 | `EL₃ = SL₃`, scalar spectral measures, finite detection, quotient and finite-extension transfer | the cited EJZK theorem for `EL₃(𝔽₂[t])`; the equality and property-(T) transport are internal |
| §5 | Infinite kernel orbits, finite-quotient displacement, and three-case ICC | none |
| §6 | Characteristic kernel, quotient twists, semisimplicity split, and cocycle obstruction | none |
| §7 | Concrete composition in `Connes.theoremA` | EJZK property (T) for `PaperPropertyT.elementaryGroup`, passed as a theorem parameter |

This is the project's locked completion boundary: the external theorem cited
by Zhou is supplied by the caller, and Zhou's own construction and proof are
formalized. No project axiom declaration is used to manufacture that input.

## Verification

The full local gate is:

```text
lake build Connes ComparatorChallenges
Build completed successfully.
```

The final axiom audit reports exactly:

```text
Connes.theoremA depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The Comparator sandbox is automated by `.github/workflows/comparator.yml`
with pinned Linux `landrun`, `lean4export`, and `nanoda` tools. The local build
and axiom audit remain separate from that sandbox verification. See
[`COMPARATOR.md`](COMPARATOR.md) for the technical trust boundary and
[`AUDITS.md`](AUDITS.md) for the semantic checks that it cannot perform.
