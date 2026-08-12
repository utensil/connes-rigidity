/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0
-/
import Connes.Construction.PaperActionInstances
import Connes.Foundation.GroupTheory.SpecialLinear.ElementaryGeneration
import Connes.Foundation.OperatorAlgebra.PropertyTTransfer
import Connes.Foundation.OperatorAlgebra.FiniteIndex
import Connes.Foundation.OperatorAlgebra.FinitePropertyT

/-!
Property-(T) transfer for Zhou §4 on the concrete tensor-kernel groups.
-/

namespace Connes
namespace PaperPropertyT

open Construction
open Construction.PaperKernel

universe u

/-- The elementary subgroup appearing in the cited EJZK theorem. Paper: §4. -/
noncomputable def elementaryGroup : CountableDiscreteGroup :=
  { Carrier := SpecialLinear.elementarySubgroup
    group := inferInstance
    countable := inferInstance }

/-- Zhou Proposition 4.1(a) identifies the elementary group with `SL₃(R)`.
Paper: §4. -/
noncomputable def elementaryEquivSL3 :
    SpecialLinear.elementarySubgroup ≃* SpecialLinear.SL3 :=
  (MulEquiv.subgroupCongr SpecialLinear.elementarySubgroup_eq_top).trans
    Subgroup.topEquiv

/-- The external EJZK property-(T) input used by Zhou §4. Paper: §4,
Proposition 4.1(b). -/
structure EJZKInput where
  propertyT : HasKazhdanPropertyT elementaryGroup

/-- Transport the cited elementary-group theorem across Zhou Proposition 4.1(a).
Paper: §4. -/
theorem sl3_propertyT_from_EJZK (input : EJZKInput) :
    HasKazhdanPropertyT SpecialLinear.sl3Group := by
  exact (OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
    elementaryGroup SpecialLinear.sl3Group elementaryEquivSL3).mp input.propertyT

/-- Inclusion of the SL₃ factor into the actual acting group. Paper: §4. -/
def sl3ToActingGroup : SpecialLinear.SL3 →* H where
  toFun l := (l, 1)
  map_one' := by rfl
  map_mul' l m := by simp

/-- The finite quotient in Zhou Proposition 4.8. Paper: §4. -/
noncomputable def finiteSymplecticGroup : CountableDiscreteGroup where
  Carrier := Q
  group := inferInstance
  countable := by infer_instance

/-- Carrier of the first actual SL₃ intermediate group. Paper: §4. -/
abbrev lambdaOneCarrierOf (actions : PaperKernel.ActionData) :=
  SemidirectProduct (Multiplicative PaperKernel.D) SpecialLinear.SL3
    (actions.thetaOne.comp sl3ToActingGroup)

/-- Carrier of the second actual SL₃ intermediate group. Paper: §4. -/
abbrev lambdaTwoCarrierOf (actions : PaperKernel.ActionData) :=
  SemidirectProduct (Multiplicative PaperKernel.D) SpecialLinear.SL3
    (actions.thetaTwo.comp sl3ToActingGroup)

/-- The SL₃ intermediate group for the first actual action. Paper: §4. -/
noncomputable def lambdaOneOf
    (actions : PaperKernel.ActionData) : CountableDiscreteGroup :=
  { Carrier := lambdaOneCarrierOf actions
    group := SemidirectProduct.instGroup
    countable := by
      exact SemidirectProduct.equivProd.injective.countable }

/-- The SL₃ intermediate group for the second actual action. Paper: §4. -/
noncomputable def lambdaTwoOf
    (actions : PaperKernel.ActionData) : CountableDiscreteGroup :=
  { Carrier := lambdaTwoCarrierOf actions
    group := SemidirectProduct.instGroup
    countable := by
      exact SemidirectProduct.equivProd.injective.countable }

/- The finite quotient Property-(T) input is discharged by averaging. Paper: §4. -/
theorem finiteSymplecticGroup_propertyT :
    HasKazhdanPropertyT finiteSymplecticGroup := by
  letI : Fintype (finiteSymplecticGroup : Type) := by
    change Fintype Q
    infer_instance
  exact PropertyTTransfer.hasKazhdanPropertyT_of_fintype finiteSymplecticGroup

end PaperPropertyT
end Connes
