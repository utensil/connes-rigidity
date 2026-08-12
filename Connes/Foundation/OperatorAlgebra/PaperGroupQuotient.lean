/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The acting-group generators of the two concrete Zhou crossed-product models.
Paper: §3.
-/
import Connes.Foundation.OperatorAlgebra.PaperGroupFactor

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace PaperGroupQuotient

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperQuotientAction
open PaperFourierCoordinates
open PaperSemidirectFubini
open PaperGroupFactor
open PaperCrossedHaar
open CrossedProduct

noncomputable section

abbrev D := PaperKernel.D
abbrev H := Construction.H

/- The first acting-group generator becomes the crossed action unitary.
Paper: §3. -/
theorem paperGroupFactorUnitaryOne_conj_inr (h : H) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : PaperGroupOne) :
          GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) =
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := paperGroupFactorUnitaryOne.surjective η
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    paperGroupFactorUnitaryOne.symm_apply_apply]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : PaperGroupOne) :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) ξ) h') =
    crossedActionL2Equiv paperHaarActionOne h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : PaperGroupOne) :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) ξ) h' =
      l2Reindex (paperThetaOneMulEquiv h)
        (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')) := by
    ext a
    rw [semidirectFubini_leftRegular_inr_apply, OpenAIPort.l2Reindex_apply]
    apply congrArg (fun b : Multiplicative D ↦
      (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')) b)
    change (paperThetaOneHom h⁻¹) a = (paperThetaOneHom h).symm a
    rw [map_inv]
    rfl
  rw [hnormal, paperFourierCoordinate_actionOne_comp]

/- The second acting-group generator becomes the crossed action unitary.
Paper: §3. -/
theorem paperGroupFactorUnitaryTwo_conj_inr (h : H) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : PaperGroupTwo) :
          GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) =
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := paperGroupFactorUnitaryTwo.surjective η
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    paperGroupFactorUnitaryTwo.symm_apply_apply]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : PaperGroupTwo) :
            GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) ξ) h') =
    crossedActionL2Equiv paperHaarActionTwo h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : PaperGroupTwo) :
            GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) ξ) h' =
      l2Reindex (paperThetaTwoMulEquiv h)
        (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')) := by
    ext a
    rw [semidirectFubini_leftRegular_inr_apply, OpenAIPort.l2Reindex_apply]
    apply congrArg (fun b : Multiplicative D ↦
      (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')) b)
    change (paperThetaTwoHom h⁻¹) a = (paperThetaTwoHom h).symm a
    rw [map_inv]
    rfl
  rw [hnormal, paperFourierCoordinate_actionTwo_comp]

end
end PaperGroupQuotient
end Connes
