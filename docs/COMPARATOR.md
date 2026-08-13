# Comparator plan

`ComparatorChallenges/F_ConnesZhou.lean` is a self-contained restatement of
the vocabulary needed for Theorem A. Its external hypothesis is exactly
property (T) for the elementary subgroup `EL₃(𝔽₂[t])` cited by Zhou, with the
same kernel-level definition as the solution statement. It imports only
`Mathlib`; it never imports `Connes` or any solution module. The configuration
lists `Connes.theoremA`, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and enables nanoda.

The Linux verification command is:

```sh
lake exe cache get
lake build Connes ComparatorChallenges
COMPARATOR_LANDRUN=... \
COMPARATOR_LEAN4EXPORT=... \
COMPARATOR_NANODA=... \
lake env comparator ComparatorChallenges/F_ConnesZhou.json
```

The full sandboxed run is a Linux/CI gate. On macOS, a build and axiom audit
are useful local evidence, but they are not a substitute for landrun plus
nanoda. The current source has one intentional `sorry`, at the independent
Comparator theorem. The solution theorem's axiom closure is exactly the
permitted set.
