# API reference

Generated declaration documentation for the `Connes` library is published at
<https://utensil.github.io/connes-rigidity/docs/>. Links through the `find`
resolver identify declarations by fully qualified name and remain valid when a
declaration moves between source files. For example:

- [`Connes.theoremA`](https://utensil.github.io/connes-rigidity/docs/find/#doc/Connes.theoremA)
- [`Connes.PaperTheoremACompletion.theoremA`](https://utensil.github.io/connes-rigidity/docs/find/#doc/Connes.PaperTheoremACompletion.theoremA)

The direct module pages and their source-line links are generated navigation,
not the stable cross-reference contract.

## Local generation

The nested `docbuild` project keeps documentation-only dependencies out of the
formalization's build graph and manifest. From a fresh checkout:

```sh
lake exe cache get
cd docbuild
ln -s ../lean-toolchain lean-toolchain
python3 sync_manifest.py
lake build doc-gen4
python3 mk_docs_root.py
DOCGEN_LOCAL_MODULE_ROOTS=Connes \
  DOCGEN_DEPS_DOCS_URL=https://leanprover-community.github.io/mathlib4_docs \
  lake build ConnesDocs:docs
```

Serve `docbuild/.lake/build/doc` over HTTP to inspect the result locally. The
generated `SOURCE_SHA` file in the deployed tree identifies the exact `main`
commit represented by the live reference.

The documentation generator is pinned independently because it uses Lean
internals. The docs manifest inherits the exact dependency revisions from the
root manifest through `sync_manifest.py`; a Lean upgrade must also verify and,
when necessary, update the doc-gen4 revision.
