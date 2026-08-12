/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped property-(T) scaffold for Zhou §4. EJZK is represented as an
explicit structure field, following the honest external-input boundary in the
evaluation. It is not declared as an axiom. The remaining analytic and
algebraic proofs are intentional skeleton obligations.
-/
import Mathlib
import Connes.Core
import Connes.Construction
import Connes.Foundation.GroupTheory.SpecialLinear
import Connes.Foundation.LinearAlgebra.BooleanPolynomial
import Connes.Foundation.OperatorAlgebra.Spectral
import Connes.Porting.CoreTransfer
import Connes.Foundation.OperatorAlgebra.FiniteIndex
import Connes.Foundation.GroupTheory.SplitAbelianExtension
import Connes.Foundation.OperatorAlgebra.PropertyTTransfer

namespace Connes
namespace PropertyT

universe u

open Construction

/-- External property-(T) input boundary. Paper: §4. -/
structure EJZKInput where
  propertyT : HasKazhdanPropertyT SpecialLinear.sl3Group

/-- Constructor for the external EJZK input. Paper: §4.

The theorem is deliberately an input rather than a project axiom: the
external property-(T) result is supplied by the caller at the construction
boundary. -/
def ejzkPropertyTInput
    (h : HasKazhdanPropertyT SpecialLinear.sl3Group) : EJZKInput :=
  ⟨h⟩

/-- Relative property-(T) for a subgroup of a countable group. Paper: §4. -/
abbrev RelativePropertyT
    (G : CountableDiscreteGroup.{u}) (N : Subgroup G) : Prop :=
  HasRelativePropertyT G N

/-- The inclusion of the `SL3` factor into the acting group. Paper: §4. -/
def sl3ToActingGroup : SpecialLinear.SL3 →* H where
  toFun l := (l, 1)
  map_one' := rfl
  map_mul' _ _ := by simp

/- The finite quotient in Zhou Proposition 4.8. -/
noncomputable def finiteSymplecticGroup : CountableDiscreteGroup where
  Carrier := Symplectic.Sp4
  group := inferInstance
  countable := by infer_instance

/-- First intermediate semidirect carrier in the property-(T) proof. Paper: §4. -/
abbrev lambdaOneCarrierOf (actions : ActionData) :=
  SemidirectProduct GammaKernel SpecialLinear.SL3
    (actions.thetaOneAction.comp sl3ToActingGroup)

/-- Second intermediate semidirect carrier in the property-(T) proof. Paper: §4. -/
abbrev lambdaTwoCarrierOf (actions : ActionData) :=
  SemidirectProduct GammaKernel SpecialLinear.SL3
    (actions.thetaTwoAction.comp sl3ToActingGroup)

/-- First intermediate group in the property-(T) proof. Paper: §4. -/
noncomputable def lambdaOneOf (actions : ActionData) :
    CountableDiscreteGroup :=
  OpenAIPort.semidirectCountableGroup kernelGroup SpecialLinear.sl3Group
    (actions.thetaOneAction.comp sl3ToActingGroup)

/-- Second intermediate group in the property-(T) proof. Paper: §4. -/
noncomputable def lambdaTwoOf (actions : ActionData) :
    CountableDiscreteGroup :=
  OpenAIPort.semidirectCountableGroup kernelGroup SpecialLinear.sl3Group
    (actions.thetaTwoAction.comp sl3ToActingGroup)

/-- First intermediate kernel subgroup. Paper: §4. -/
noncomputable def lambdaOneKernelSubgroup (actions : ActionData) :
    Subgroup (lambdaOneOf actions) :=
  (⊥ : Subgroup SpecialLinear.SL3).comap
    (SemidirectProduct.rightHom
      (φ := actions.thetaOneAction.comp sl3ToActingGroup))

/-- Second intermediate kernel subgroup. Paper: §4. -/
noncomputable def lambdaTwoKernelSubgroup (actions : ActionData) :
    Subgroup (lambdaTwoOf actions) :=
  (⊥ : Subgroup SpecialLinear.SL3).comap
    (SemidirectProduct.rightHom
      (φ := actions.thetaTwoAction.comp sl3ToActingGroup))

/-- Inputs for the two relative-property-(T) applications in Zhou §4. -/
structure PropertyTData (actions : ActionData) where
  lambdaOne : PropertyTTransfer.RelativeExtensionData
    (lambdaOneOf actions) SpecialLinear.sl3Group
    (lambdaOneKernelSubgroup actions)
  lambdaTwo : PropertyTTransfer.RelativeExtensionData
    (lambdaTwoOf actions) SpecialLinear.sl3Group
    (lambdaTwoKernelSubgroup actions)
  gammaOne : PropertyTTransfer.FiniteExtensionData
    (lambdaOneOf actions) (gammaOneOf actions) finiteSymplecticGroup
  gammaTwo : PropertyTTransfer.FiniteExtensionData
    (lambdaTwoOf actions) (gammaTwoOf actions) finiteSymplecticGroup
  finiteQuotient_propertyT : HasKazhdanPropertyT finiteSymplecticGroup

/-- Property-(T) transfer from the external input. Paper: §4. -/
theorem sl3_propertyT_from_EJZK (input : EJZKInput) :
    HasKazhdanPropertyT SpecialLinear.sl3Group :=
  input.propertyT

/-- Property-(T) descends through a proved surjective quotient. Paper: §4. -/
theorem propertyT_of_surjective
    (G H : CountableDiscreteGroup.{u}) (f : G →* H)
    (hf : Function.Surjective f) (hG : HasKazhdanPropertyT G) :
    HasKazhdanPropertyT H :=
  OpenAIPort.hasKazhdanPropertyT_of_surjective G H f hf hG

/-- Property-(T) descends to a proved finite-index subgroup. Paper: §4. -/
theorem propertyT_of_finiteIndex
    (G : CountableDiscreteGroup.{u}) (S : Subgroup G)
    [S.FiniteIndex] (hG : HasKazhdanPropertyT G) :
    HasKazhdanPropertyT (OpenAIPort.CountableDiscreteGroup.subgroup G S) :=
  OpenAIPort.hasKazhdanPropertyT_subgroup_of_finiteIndex G S hG

/-- Property-(T) for the two intermediate groups supplied by the §4 spectral
boundary and the EJZK property-(T) input. Paper: §4. -/
theorem lambdaOne_propertyT
    (actions : ActionData) (input : EJZKInput)
    (data : PropertyTData actions) :
    HasKazhdanPropertyT (lambdaOneOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_relative_and_quotient
    (lambdaOneOf actions) (lambdaOneKernelSubgroup actions)
    data.lambdaOne.normal data.lambdaOne.relative
    ((OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
      (CountableDiscreteGroup.quotient
        (lambdaOneOf actions) (lambdaOneKernelSubgroup actions)
        data.lambdaOne.normal)
      SpecialLinear.sl3Group data.lambdaOne.quotientEquiv).mpr input.propertyT)

/-- Property-(T) for the second intermediate group supplied by the §4
spectral boundary and the EJZK property-(T) input. Paper: §4. -/
theorem lambdaTwo_propertyT
    (actions : ActionData) (input : EJZKInput)
    (data : PropertyTData actions) :
    HasKazhdanPropertyT (lambdaTwoOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_relative_and_quotient
    (lambdaTwoOf actions) (lambdaTwoKernelSubgroup actions)
    data.lambdaTwo.normal data.lambdaTwo.relative
    ((OpenAIPort.hasKazhdanPropertyT_iff_of_mulEquiv
      (CountableDiscreteGroup.quotient
        (lambdaTwoOf actions) (lambdaTwoKernelSubgroup actions)
        data.lambdaTwo.normal)
      SpecialLinear.sl3Group data.lambdaTwo.quotientEquiv).mpr input.propertyT)

/-- First group property-(T) conclusion for supplied paper data. Paper: §4. -/
theorem gammaOne_propertyT
    (actions : ActionData) (input : EJZKInput)
    (data : PropertyTData actions) :
    HasKazhdanPropertyT (gammaOneOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    data.gammaOne (lambdaOne_propertyT actions input data)
    data.finiteQuotient_propertyT

/-- Second group property-(T) conclusion for supplied paper data. Paper: §4. -/
theorem gammaTwo_propertyT
    (actions : ActionData) (input : EJZKInput)
    (data : PropertyTData actions) :
    HasKazhdanPropertyT (gammaTwoOf actions) := by
  exact PropertyTTransfer.hasKazhdanPropertyT_of_finiteExtension
    data.gammaTwo (lambdaTwo_propertyT actions input data)
    data.finiteQuotient_propertyT

/-- Property-(T) completion pair for supplied paper data. Paper: §4. -/
theorem propertyT_completion
    (actions : ActionData) (input : EJZKInput)
    (data : PropertyTData actions) :
    HasKazhdanPropertyT (gammaOneOf actions) ∧
      HasKazhdanPropertyT (gammaTwoOf actions) := by
  exact ⟨gammaOne_propertyT actions input data,
    gammaTwo_propertyT actions input data⟩

end PropertyT
end Connes
