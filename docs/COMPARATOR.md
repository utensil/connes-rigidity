# Comparator plan

`ComparatorChallenges/F_ConnesZhou.lean` is a self-contained restatement of
the vocabulary needed for Theorem A. Its external hypothesis is exactly
property (T) for the elementary subgroup `EL₃(𝔽₂[t])` cited by Zhou, with the
same kernel-level definition as the solution statement. It imports only
`Mathlib`; it never imports `Connes` or any solution module. The configuration
lists `Connes.theoremA`, permits only `propext`, `Quot.sound`, and
`Classical.choice`, and enables nanoda.

The ordinary local build is:

```sh
lake exe cache get
lake build Connes ComparatorChallenges
```

The full sandboxed run is a separate Linux/CI gate in a fresh checkout. It
prepares only trusted dependency caches and verifier binaries before letting
Comparator build the challenge and solution inside landrun. On macOS, a build
and axiom audit are useful local evidence, but they are not a substitute for
landrun plus nanoda. The current source has one intentional `sorry`, at the
independent Comparator theorem. The solution theorem's axiom closure is
exactly the permitted set.

The repository workflow runs a pre-merge gate on same-repository pull requests
and the authoritative gate on pushes to `main` and manual dispatches. Fork
pull requests are excluded because no candidate Lean module may be built
outside Comparator's sandbox. The workflow pins Comparator and
`lean4export` through Lake, pins landrun and nanoda by commit, self-tests
Landlock confinement, and invokes Comparator inside an outer `systemd-run`
network guard without repository credentials or secrets.
