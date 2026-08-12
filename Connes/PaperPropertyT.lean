/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-facing property-(T) transfer for Zhou §4. The older `PropertyT` file
targets the retired placeholder carrier; this file instantiates the same
proved transfer lemmas at `Construction.PaperKernel`.
-/
import Connes.Construction.PaperActionInstances
import Connes.Foundation.OperatorAlgebra.PropertyTTransfer
import Connes.Foundation.OperatorAlgebra.FiniteIndex
import Connes.Foundation.OperatorAlgebra.FinitePropertyT

namespace Connes
namespace PaperPropertyT

open Construction
open Construction.PaperKernel

universe u

/-- The external EJZK property-(T) input used by Zhou §4. Paper: §4. -/
structure EJZKInput where
  propertyT : HasKazhdanPropertyT SpecialLinear.sl3Group

/-- The acting group in the actual paper construction. Paper: §2, §4. -/
noncomputable def actingGroup : CountableDiscreteGroup where
  Carrier := H
  group := inferInstance
  countable := by infer_instance

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

/-- The kernel subgroup of the first actual intermediate group. Paper: §4. -/
noncomputable def lambdaOneKernelSubgroup
    (actions : PaperKernel.ActionData) : Subgroup (lambdaOneOf actions) :=
  by
    exact (⊥ : Subgroup SpecialLinear.SL3).comap
      (SemidirectProduct.rightHom
        (N := Multiplicative PaperKernel.D)
        (G := SpecialLinear.SL3)
        (φ := actions.thetaOne.comp sl3ToActingGroup))

/-- The kernel subgroup of the second actual intermediate group. Paper: §4. -/
noncomputable def lambdaTwoKernelSubgroup
    (actions : PaperKernel.ActionData) : Subgroup (lambdaTwoOf actions) :=
  by
    exact (⊥ : Subgroup SpecialLinear.SL3).comap
      (SemidirectProduct.rightHom
        (N := Multiplicative PaperKernel.D)
        (G := SpecialLinear.SL3)
        (φ := actions.thetaTwo.comp sl3ToActingGroup))

/-- The paper's spectral and finite-index inputs, on the actual carriers.
The relative fields are the output of the §4 spectral argument; the quotient
equivalences and finite-index fields are the group-theoretic identifications
used in Zhou Lemma 4.7 and Proposition 4.8. Paper: §4. -/
structure Data (actions : PaperKernel.ActionData) where
  lambdaOne : PropertyTTransfer.RelativeExtensionData
    (lambdaOneOf actions) SpecialLinear.sl3Group
    (lambdaOneKernelSubgroup actions)
  lambdaTwo : PropertyTTransfer.RelativeExtensionData
    (lambdaTwoOf actions) SpecialLinear.sl3Group
    (lambdaTwoKernelSubgroup actions)
  gammaOne : PropertyTTransfer.FiniteExtensionData
    (lambdaOneOf actions) (paperGammaOneOf actions) finiteSymplecticGroup
  gammaTwo : PropertyTTransfer.FiniteExtensionData
    (lambdaTwoOf actions) (paperGammaTwoOf actions) finiteSymplecticGroup

/- The finite quotient Property-(T) input is discharged by averaging. Paper: §4. -/
theorem finiteSymplecticGroup_propertyT :
    HasKazhdanPropertyT finiteSymplecticGroup := by
  letI : Fintype (finiteSymplecticGroup : Type) := by
    change Fintype Q
    infer_instance
  exact PropertyTTransfer.hasKazhdanPropertyT_of_fintype finiteSymplecticGroup

/-- The actual first intermediate group has property-(T). Paper: §4. -/
theorem lambdaOne_propertyT
    (actions : PaperKernel.ActionData) (input : EJZKInput) (data : Data actions) :
    HasKazhdanPropertyT (lambdaOneOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_relative_and_quotient
    (lambdaOneOf actions) (lambdaOneKernelSubgroup actions)
    data.lambdaOne.normal data.lambdaOne.relative
    ((OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
      (CountableDiscreteGroup.quotient
        (lambdaOneOf actions) (lambdaOneKernelSubgroup actions)
        data.lambdaOne.normal)
      SpecialLinear.sl3Group data.lambdaOne.quotientEquiv).mpr input.propertyT)

/-- The actual second intermediate group has property-(T). Paper: §4. -/
theorem lambdaTwo_propertyT
    (actions : PaperKernel.ActionData) (input : EJZKInput) (data : Data actions) :
    HasKazhdanPropertyT (lambdaTwoOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_relative_and_quotient
    (lambdaTwoOf actions) (lambdaTwoKernelSubgroup actions)
    data.lambdaTwo.normal data.lambdaTwo.relative
    ((OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
      (CountableDiscreteGroup.quotient
        (lambdaTwoOf actions) (lambdaTwoKernelSubgroup actions)
        data.lambdaTwo.normal)
      SpecialLinear.sl3Group data.lambdaTwo.quotientEquiv).mpr input.propertyT)

/-- Property-(T) for the first actual Zhou group. Paper: §4. -/
theorem gammaOne_propertyT
    (actions : PaperKernel.ActionData) (input : EJZKInput) (data : Data actions) :
    HasKazhdanPropertyT (paperGammaOneOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    data.gammaOne (lambdaOne_propertyT actions input data)
    finiteSymplecticGroup_propertyT

/-- Property-(T) for the second actual Zhou group. Paper: §4. -/
theorem gammaTwo_propertyT
    (actions : PaperKernel.ActionData) (input : EJZKInput) (data : Data actions) :
    HasKazhdanPropertyT (paperGammaTwoOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    data.gammaTwo (lambdaTwo_propertyT actions input data)
    finiteSymplecticGroup_propertyT

/-- The actual pair of §4 conclusions. Paper: §4. -/
theorem completion
    (actions : PaperKernel.ActionData) (input : EJZKInput) (data : Data actions) :
    HasKazhdanPropertyT (paperGammaOneOf actions) ∧
      HasKazhdanPropertyT (paperGammaTwoOf actions) := by
  exact ⟨gammaOne_propertyT actions input data,
    gammaTwo_propertyT actions input data⟩

end PaperPropertyT
end Connes
