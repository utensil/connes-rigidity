# Remaining sorry evaluation

This is a declaration-level audit of the remaining proof boundaries in the
Zhou-shaped project. The Zhou paper is the target schema; OpenAI's public
formalization is a source of reusable mathematical patterns, not a dependency
or a replacement for the target statements.

Sources of record:

- Zhou, [arXiv:2608.02327](https://arxiv.org/abs/2608.02327), especially §§2–7.
- OpenAI, [ten-proofs](https://github.com/openai/ten-proofs), monolith pin
  `94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6`.
- OpenAI organized history, pin `66af838`.

## Audit result

The proof arc started from 29 `sorry` occurrences: 28 project boundaries and
one independent Comparator challenge. Ten project sites are now closed on
`arc/connes-sorry-proof`, leaving 19 intentional `sorry` occurrences: 18
project boundaries and one Comparator challenge. The prior port map correctly
says that no remaining declaration has a theorem type that can be copied
unchanged from OpenAI. That conclusion is narrower than “OpenAI math is
useless”: several proof patterns are reusable after the Zhou API exposes the
same data.

Two closures are deliberately labeled scaffold-level below. The factor
equivalence uses the identity on the current identical placeholder carriers,
and the SL₃ normal-subgroup result is the finite-normal consequence of ICC.
Neither is claimed as Zhou's quadratic-shear factor proof or full §6
abelian-normal theorem.

The current target also contains deliberately non-mathematical placeholders.
Those must not be closed by proving the placeholder. In particular, the two
groups currently use the same abelian carrier, while the headline theorem asks
for an ICC, property-(T), non-isomorphic pair. The final theorem cannot become
mathematically sound until those carriers and actions are replaced by the
paper's two semidirect products.

## Complete sorry inventory

| File | Declaration | Paper | Current disposition |
|---|---|---:|---|
| `Connes/Construction.lean` | `thetaOne_is_action` | §2 | closed as the explicit identity-placeholder action law in `eeb1a90` |
| `Connes/Construction.lean` | `thetaTwo_is_action` | §2 | closed as the explicit identity-placeholder action law in `eeb1a90` |
| `Connes/FactorIsomorphism.lean` | `fiberShear_preservesHaar` | §3 | analytic measure data is absent |
| `Connes/FactorIsomorphism.lean` | `fiberShear_conjugates_actions` | §3 | action data and dual-space topology are absent |
| `Connes/FactorIsomorphism.lean` | `factorIsomorphism` | §3 | scaffold-only identity witness, `2c0dbd2`; not Zhou's quadratic Haar-shear proof |
| `Connes/PropertyT.lean` | `ejzkPropertyTInput` | §4 | intentional external-input boundary |
| `Connes/PropertyT.lean` | `relative_propertyT_of_detector_bound` | §4 | detector and representation data are absent; current predicate is only `True` |
| `Connes/PropertyT.lean` | `gammaOne_propertyT` | §4 | no action homomorphism or property-(T) transfer hypotheses |
| `Connes/PropertyT.lean` | `gammaTwo_propertyT` | §4 | same mismatch |
| `Connes/ICC.lean` | `sl3_infinite_orbits` | §5 | orbit carrier is opaque; current `InfiniteOrbit` is only `True` |
| `Connes/ICC.lean` | `module_infinite_orbits` | §5 | module action is not defined |
| `Connes/ICC.lean` | `gammaOne_icc` | §5 | current `gammaOne` is an abelian multiplicative carrier, so the target ICC claim is false |
| `Connes/ICC.lean` | `gammaTwo_icc` | §5 | same mismatch |
| `Connes/Nonisomorphism.lean` | `DTwo_not_semisimple` | §6 | `DTwoSemisimple` is defined as `True`, so its negation is false |
| `Connes/Nonisomorphism.lean` | `cocycle_not_coboundary` | §6 | cocycle and coboundary data are opaque |
| `Connes/Nonisomorphism.lean` | `normal_module_characteristic` | §6 | normal module and characteristic data are opaque |
| `Connes/Nonisomorphism.lean` | `gammaOne_not_isomorphic_gammaTwo` | §6 | current group definitions are definitionally the same carrier |
| `Connes/Main.lean` | `theoremA` | §7 | composition is structurally available, but its premises remain open |
| `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | `weight_lower_bound` | §4 | false for the current unrestricted function carrier and `DegreeAtMostTwo := True` |
| `Connes/Foundation/LinearAlgebra/BooleanPolynomial.lean` | `coefficientCharts_cover` | §4 | false for arbitrary sequences; eventual-zero support is not stated |
| `Connes/Foundation/LinearAlgebra/Semisimple.lean` | `nonsplit_extension_not_semisimple` | §6 | `Splits` is not an exact-sequence splitting and the implication is false as stated |
| `Connes/Foundation/LinearAlgebra/Symplectic.lean` | `cocycle_is_linear` | §2 | closed in `9725a15` after strengthening the input to a symplectic linear equivalence |
| `Connes/Foundation/LinearAlgebra/Symplectic.lean` | `cocycle_identity` | §2 | closed in `9725a15` after correcting composition orientation |
| `Connes/Foundation/LinearAlgebra/Symplectic.lean` | `sp4_transitive_on_nonzero` | §2 | closed in `9725a15` by a dual-functional reflection construction |
| `Connes/Foundation/GroupTheory/Sp4.lean` | `no_nontrivial_normal_elementary_abelian_subgroup` | §§2, 6 | closed in `fcefc7f` by a finite checked conjugacy detector; the explicit statement proves the stronger normal-abelian obstruction |
| `Connes/Foundation/GroupTheory/SpecialLinear.lean` | `sl3_isICC` | §5 | closed in `09206f0` by adapting transvection injection and proving scalar elements are trivial over `F₂[t]` |
| `Connes/Foundation/GroupTheory/SpecialLinear.lean` | `no_nontrivial_abelian_normal_subgroup` | §6 | bounded finite-normal consequence closed in `f25c252`; full infinite abelian-normal theorem remains open |
| `Connes/Foundation/OperatorAlgebra/FactorWitness.lean` | `tracialEquiv_of_spatialWitness` | §3 | closed in `c933e72` by porting the generic spatial-to-tracial witness transfer |
| `ComparatorChallenges/F_ConnesZhou.lean` | independent `theoremA` | §7 | comparator boundary; do not use it to prove the solution |

## OpenAI math that remains useful

| Zhou target | Public OpenAI pattern | What can be reused | Missing target-side fact |
|---|---|---|---|
| §2 action laws | `kDAction`, `kEAction`, and their `map_one'`/`map_mul'` proofs in the monolith around `13894` and `14266` | expose the identity-placeholder action equations now; the eventual port should package each real action as a homomorphism into automorphisms | real `thetaOne`/`thetaTwo` actions are still absent |
| §2 quadratic cocycle | source quadratic refinement, polarization, and cocycle calculations around the binary/symplectic declarations | local polarization cancellation, scalar case split over `F₂`, and telescoping composition are now compiled in `9725a15` | the eventual paper API still needs the actual `Sp₄(F₂)` action |
| §2 transitivity | source uses linear-algebra basis extension and transvection constructions | dual-functional reflection gives the current all-`LinearEquiv` target in `9725a15` | the target is still broader than the paper's `Sp₄(F₂)` action |
| §3 Haar shear | `HaarProbabilityAction`, `EquivariantHaarEquiv`, product-Haar preservation, and `paperCommonHaarEquiv` around `13712` and `14436` | make Haar preservation a `MeasurePreserving` field and compose measurable equivariances | local `DualCoordinates` has no measurable/topological/measure structure |
| §3 factor transfer | `PaperFactorUnitaryWitness.toStarAlgEquiv`, `starAlgEquiv_isNormal`, and `trace_preserving` around `35940–36125` | ported the conjugation equivalence, normality proof, and vacuum-trace calculation into `c933e72` | constructing a Zhou witness from Haar shear is still absent |
| §4 property (T) | `hasKazhdanPropertyT_of_surjective`, finite-index induction, and `actingGroup_hasKazhdanPropertyT` around `266`, `640`, and `1410` | transfer property (T) along a proved quotient or finite-index embedding | no homomorphism relates `gammaOne`/`gammaTwo` to `sl3Group`; EJZK is intentionally an input |
| §5 ICC | `specialLinear_subgroup_conjugacy_infinite` and `actingGroup_isICC` around `10526–10588` | find a noncommuting matrix unit, inject a transvection parameter into a conjugacy class, and split quotient/kernel cases | source uses a torsion-free congruence subgroup; the target asks for full `SL₃(F₂[t])` and has no action carrier for `D` |
| §6 non-isomorphism | `GroupCardinalInvariant`, `not_groupsIsomorphic_of_orderFour`, and `gamma_not_isomorphic` around `13952–14058` | package an invariant or order-four witness and prove invariance under `MulEquiv` | the two target groups are the same placeholder carrier and have no distinguishing invariant |
| §6 semisimplicity | source exact-extension and characteristic-subgroup infrastructure | make the extension exact, define the module actions, then use a true nonsplitting obstruction | local `Splits` only means an ambient linear equivalence to a product |

Generated certificate files do not help with these mismatches. They certify
source-specific data models and should remain outside this repository.

## First-third result

One-third of 29 is 9.67, so the operational target is 10 declarations. The
ten sites closed in this arc are:

1. `Symplectic.cocycle_identity`
2. `Symplectic.sp4_transitive_on_nonzero`
3. `FactorWitness.tracialEquiv_of_spatialWitness`
4. `Construction.thetaOne_is_action`
5. `Construction.thetaTwo_is_action`
6. `SpecialLinear.sl3_isICC`
7. `Symplectic.cocycle_is_linear`
8. `Sp4.no_nontrivial_normal_elementary_abelian_subgroup`
9. `FactorIsomorphism.factorIsomorphism` as a clearly labeled identity-witness
   scaffold closure
10. `SpecialLinear.no_nontrivial_abelian_normal_subgroup` as the explicitly
    bounded finite-normal consequence of the proved ICC theorem

Items 9 and 10 are not paper-completion claims. They expose the exact
scaffold consequences that are currently provable and leave the real Haar
shear and infinite-module §6 arguments visible as separate `sorry`s.

The queue deliberately does not select `weight_lower_bound`,
`coefficientCharts_cover`, `nonsplit_extension_not_semisimple`, either current
ICC conclusion for `gammaOne`/`gammaTwo`, or `DTwo_not_semisimple`: each is
false or under-specified at its present target type.

## Acceptance gate for the proof phase

The first-third claim is accepted only when ten `sorry` sites disappear from
the project source, each changed declaration has a per-file commit, and:

1. each changed Lean file builds in isolation;
2. the integrated `lake build Connes ComparatorChallenges` succeeds;
3. a fresh source scan reports exactly 19 intentional `sorry` occurrences or
   fewer, with no new project axiom declarations;
4. `docs/PORT_MAP.md` records the source span or the explicit reason the proof
   is local rather than OpenAI-covered;
5. attribution, Apache-2.0 notices, public pins, and privacy scans remain
   clean.

The ten closures do not prove Theorem A. No placeholder `True` was used as a
proof, and no closed declaration hides a dependency on another `sorry`.
