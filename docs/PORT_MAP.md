# OpenAI proof-port map

The port arc treats the public OpenAI file as an archive of proof blocks, not
as a dependency. The source is the exact public snapshot
`94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`; no local or private checkout is a
source for tracked files.

## Per-file method

1. Locate a declaration in the pinned public snapshot.
2. Extract its complete source block with
   `scripts/extract-openai-slice` into the review buffer.
3. Put the block in the smallest matching project file, changing only
   namespace, imports, and explicitly recorded name adaptations.
4. Build that file's target before moving to the next file.
5. Record whether the transfer is exact, adapted, or not applicable.

The extractor only prints a requested revision and line range. It never edits
the repository, and it does not accept a URL or an implicit current checkout.

## Current ledger

| Zhou area | Project file | OpenAI source block | Status |
| --- | --- | --- | --- |
| §3 factor vocabulary | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:137-157` | proof transfer with namespace adaptation |
| §4 property-(T) transfer | `Connes/Porting/CoreTransfer.lean` | `ConnesRigidity.lean:252-285` | proof transfer with namespace adaptation |
| §2 construction | `Connes/Construction.lean` | OpenAI tensor and action blocks | not type-compatible with the Zhou interface; retain skeleton boundary |
| §3 analytic shear | `Connes/FactorIsomorphism.lean` | OpenAI factor blocks | different group and dual data; port by later local slice |
| §4 detector argument | `Connes/PropertyT.lean` | OpenAI detector blocks | different external input boundary; port by later local slice |
| §5 ICC | `Connes/ICC.lean` | OpenAI conjugacy blocks | different group construction; port by later local slice |
| §6 nonisomorphism | `Connes/Nonisomorphism.lean` | OpenAI characteristic-subgroup blocks | different invariant; port by later local slice |

The historical organized OpenAI tree is useful for dependency ordering, but it
contains thousands of generated certificate files. The port boundary keeps
those artifacts out of this repository and follows the Zhou section/file
split instead.
