/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete Zhou group-factor Hilbert models.  The carrier is the semidirect
product from §2 and the base is the Fourier crossed-product model from §3.
-/
import Connes.Foundation.OperatorAlgebra.SemidirectFubini
import Connes.Paper.Section3.CrossedKernel
import Connes.Paper.Section3.QuotientAction

namespace Connes
namespace PaperGroupFactor

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperFourierCoordinates
open PaperCrossedHaar
open PaperCrossedKernel
open SemidirectFubini
open CrossedProduct

noncomputable section

abbrev D := PaperKernel.D
abbrev H := Construction.H
local notation "Γ₁" => PaperKernel.paperGammaCarrier paperThetaOneHom
local notation "Γ₂" => PaperKernel.paperGammaCarrier paperThetaTwoHom
abbrev CrossedOne := crossedHilbert paperHaarActionOne
abbrev CrossedTwo := crossedHilbert paperHaarActionTwo

/- The first concrete Zhou group-factor unitary. Paper: §3. -/
def paperGroupFactorUnitaryOne :
    GroupL2 Γ₁ ≃ₗᵢ[ℂ] CrossedOne :=
  (semidirectFubini paperThetaOneHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)

/- The second concrete Zhou group-factor unitary. Paper: §3. -/
def paperGroupFactorUnitaryTwo :
    GroupL2 Γ₂ ≃ₗᵢ[ℂ] CrossedTwo :=
  (semidirectFubini paperThetaTwoHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)

@[simp] theorem paperGroupFactorUnitaryOne_apply
    (ξ : GroupL2 Γ₁) (h : H) :
    paperGroupFactorUnitaryOne ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaOneHom ξ h) := rfl

@[simp] theorem paperGroupFactorUnitaryTwo_apply
    (ξ : GroupL2 Γ₂) (h : H) :
    paperGroupFactorUnitaryTwo ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaTwoHom ξ h) := rfl

/- Kernel translations become the concrete crossed-base multipliers for the
first Zhou factor. Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.
set_option maxHeartbeats 1600000 in
theorem paperGroupFactorUnitaryOne_conj_inl (d : D) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
          GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) =
      crossedKernelMultiplier d := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryOne.symm η
  have hη : paperGroupFactorUnitaryOne ξ = η :=
    paperGroupFactorUnitaryOne.apply_symm_apply η
  let T : GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁ :=
    leftRegularUnitary
      (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁)
  have hconj :=
    (LinearIsometryEquiv.conjStarAlgEquiv_apply_apply
      paperGroupFactorUnitaryOne T (paperGroupFactorUnitaryOne ξ)).trans
      (congrArg (fun x => paperGroupFactorUnitaryOne (T x))
        (paperGroupFactorUnitaryOne.symm_apply_apply ξ))
  rw [← hη, hconj]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
            GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionOne
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaOneHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₁) :
              GroupL2 Γ₁ →L[ℂ] GroupL2 Γ₁) ξ) h =
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
          (semidirectFubini paperThetaOneHom ξ h) := by
    ext a
    rw [semidirectFubini_leftRegular_inl_apply]
    rfl
  rw [hfiber]
  have hkernel := congrArg
      (fun T : PaperFourierCoordinates.CoordinateL2 →L[ℂ]
          PaperFourierCoordinates.CoordinateL2 =>
        T (paperFourierCoordinateUnitary
          (semidirectFubini paperThetaOneHom
            ξ h)))
      (paperFourierCoordinate_conjugates_regular d)
  rw [coordinateCharacterMultiplier_eq_baseMultiplier] at hkernel
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hkernel
  rw [paperFourierCoordinateUnitary.symm_apply_apply] at hkernel
  change paperFourierCoordinateUnitary
      ((leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
        (semidirectFubini paperThetaOneHom ξ h)) =
    crossedBaseMultiplier paperHaarActionOne
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom ξ h)) at hkernel
  exact hkernel

/- Kernel translations become the concrete crossed-base multipliers for the
second Zhou factor. Paper: §3. -/
-- The nested L² transport normalization exceeds Lean's default
-- elaboration budget.
set_option maxHeartbeats 1600000 in
theorem paperGroupFactorUnitaryTwo_conj_inl (d : D) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
          GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) =
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) := by
  apply ContinuousLinearMap.ext
  intro η
  let ξ := paperGroupFactorUnitaryTwo.symm η
  have hη : paperGroupFactorUnitaryTwo ξ = η :=
    paperGroupFactorUnitaryTwo.apply_symm_apply η
  let T : GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂ :=
    leftRegularUnitary
      (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂)
  have hconj :=
    (LinearIsometryEquiv.conjStarAlgEquiv_apply_apply
      paperGroupFactorUnitaryTwo T (paperGroupFactorUnitaryTwo ξ)).trans
      (congrArg (fun x => paperGroupFactorUnitaryTwo (T x))
        (paperGroupFactorUnitaryTwo.symm_apply_apply ξ))
  rw [← hη, hconj]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
            GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionTwo
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaTwoHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : Γ₂) :
              GroupL2 Γ₂ →L[ℂ] GroupL2 Γ₂) ξ) h =
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
          (semidirectFubini paperThetaTwoHom ξ h) := by
    ext a
    rw [semidirectFubini_leftRegular_inl_apply]
    rfl
  rw [hfiber]
  have hkernel := congrArg
      (fun T : PaperFourierCoordinates.CoordinateL2 →L[ℂ]
          PaperFourierCoordinates.CoordinateL2 =>
        T (paperFourierCoordinateUnitary
          (semidirectFubini paperThetaTwoHom
            ξ h)))
      (paperFourierCoordinate_conjugates_regular d)
  rw [coordinateCharacterMultiplier_eq_baseMultiplier] at hkernel
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] at hkernel
  rw [paperFourierCoordinateUnitary.symm_apply_apply] at hkernel
  change paperFourierCoordinateUnitary
      ((leftRegularUnitary (Multiplicative.ofAdd d) :
        GroupL2 (Multiplicative D) →L[ℂ] GroupL2 (Multiplicative D))
        (semidirectFubini paperThetaTwoHom ξ h)) =
    crossedBaseMultiplier paperHaarActionTwo
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom ξ h)) at hkernel
  exact hkernel

end
end PaperGroupFactor
end Connes
