/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The acting-group generators of the two concrete Zhou crossed-product models.
Paper: §3.
-/
import Connes.Paper.Section3.GroupFactor

namespace Connes
namespace PaperGroupQuotient

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperQuotientAction
open PaperFourierCoordinates
open SemidirectFubini
open PaperGroupFactor
open PaperCrossedHaar
open CrossedProduct

noncomputable section

abbrev D := PaperKernel.D
abbrev H := Construction.H
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom

/- The first acting-group generator becomes the crossed action unitary.
Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.
set_option maxHeartbeats 1600000 in
theorem paperGroupFactorUnitaryOne_conj_inr (h : H) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : Γ₁) :
          GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) =
      (crossedGroupUnitary paperHaarActionOne h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryOne.symm η
  have hη : paperGroupFactorUnitaryOne ξ = η :=
    paperGroupFactorUnitaryOne.apply_symm_apply η
  let T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁ :=
    leftRegularUnitary (SemidirectProduct.inr h : Γ₁)
  have hconj :=
    (LinearIsometryEquiv.conjStarAlgEquiv_apply_apply
      paperGroupFactorUnitaryOne T (paperGroupFactorUnitaryOne ξ)).trans
      (congrArg (fun x => paperGroupFactorUnitaryOne (T x))
        (paperGroupFactorUnitaryOne.symm_apply_apply ξ))
  rw [← hη, hconj]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h') =
    crossedActionL2Equiv paperHaarActionOne h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h' =
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
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.
set_option maxHeartbeats 1600000 in
theorem paperGroupFactorUnitaryTwo_conj_inr (h : H) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inr h : Γ₂) :
          GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) =
      (crossedGroupUnitary paperHaarActionTwo h).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryTwo.symm η
  have hη : paperGroupFactorUnitaryTwo ξ = η :=
    paperGroupFactorUnitaryTwo.apply_symm_apply η
  let T : GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂ :=
    leftRegularUnitary (SemidirectProduct.inr h : Γ₂)
  have hconj :=
    (LinearIsometryEquiv.conjStarAlgEquiv_apply_apply
      paperGroupFactorUnitaryTwo T (paperGroupFactorUnitaryTwo ξ)).trans
      (congrArg (fun x => paperGroupFactorUnitaryTwo (T x))
        (paperGroupFactorUnitaryTwo.symm_apply_apply ξ))
  rw [← hη, hconj]
  apply lp.ext
  funext h'
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h') =
    crossedActionL2Equiv paperHaarActionTwo h
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom ξ (h⁻¹ * h')))
  have hnormal :
      semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inr h : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h' =
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
