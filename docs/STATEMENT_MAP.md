# Statement map

The names below are the stable skeleton boundary. Their bodies are open.

| Paper | Lean declaration |
| --- | --- |
| Lemma 2.1, diagonal retraction | `Connes.Construction.delta_diagonal` |
| Lemma 2.2, symplectic cocycle | `Connes.Symplectic.cocycle_is_linear` |
| Lemma 2.3, actions | `Connes.Construction.thetaOne_is_action`, `thetaTwo_is_action` |
| Proposition 3.2, fiber shear | `Connes.FactorIsomorphism.fiberShear_preservesHaar`, `fiberShear_conjugates_actions` |
| Proposition 3.4, factor isomorphism | `Connes.FactorIsomorphism.groupFactors_isomorphic` |
| Proposition 4.1(a), elementary generation | `Connes.SpecialLinear.sl3_eq_elementary` |
| Proposition 4.1(b), EJZK input | `Connes.PropertyT.EJZKInput` |
| Lemma 4.3, Boolean weight | `Connes.BooleanPolynomial.weight_lower_bound` |
| Proposition 4.8, property (T) | `Connes.PropertyT.gammaOne_propertyT`, `gammaTwo_propertyT` |
| Proposition 5.3, ICC | `Connes.ICC.gammaOne_icc`, `gammaTwo_icc` |
| Proposition 6.5, non-isomorphism | `Connes.Nonisomorphism.gammaOne_not_isomorphic_gammaTwo` |
| Theorem A | `Connes.theoremA` |

The comparator challenge is the public, independent statement record for the
last row. It deliberately does not import any of the declarations above.
