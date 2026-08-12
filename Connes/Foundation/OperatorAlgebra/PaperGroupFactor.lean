/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete Zhou group-factor Hilbert models.  The carrier is the semidirect
product from §2 and the base is the Fourier crossed-product model from §3.
-/
import Connes.Foundation.OperatorAlgebra.PaperSemidirectFubini
import Connes.Foundation.OperatorAlgebra.PaperCrossedKernel
import Connes.Foundation.OperatorAlgebra.PaperQuotientAction

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace PaperGroupFactor

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperFourierCoordinates
open PaperCrossedHaar
open PaperCrossedKernel
open PaperSemidirectFubini
open CrossedProduct

noncomputable section

abbrev D := PaperKernel.D
abbrev H := Construction.H
abbrev Kernel := Multiplicative D
abbrev PaperGroupOne := SemidirectProduct Kernel H paperThetaOneHom
abbrev PaperGroupTwo := SemidirectProduct Kernel H paperThetaTwoHom
abbrev CrossedOne := crossedHilbert paperHaarActionOne
abbrev CrossedTwo := crossedHilbert paperHaarActionTwo

/- The first concrete Zhou group-factor unitary. Paper: §3. -/
def paperGroupFactorUnitaryOne :
    GroupL2 PaperGroupOne ≃ₗᵢ[ℂ] CrossedOne :=
  (semidirectFubini paperThetaOneHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)

/- The second concrete Zhou group-factor unitary. Paper: §3. -/
def paperGroupFactorUnitaryTwo :
    GroupL2 PaperGroupTwo ≃ₗᵢ[ℂ] CrossedTwo :=
  (semidirectFubini paperThetaTwoHom).trans
    (crossedFiberwiseEquiv (K := H) paperFourierCoordinateUnitary)

@[simp] theorem paperGroupFactorUnitaryOne_apply
    (ξ : GroupL2 PaperGroupOne) (h : H) :
    paperGroupFactorUnitaryOne ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaOneHom ξ h) := rfl

@[simp] theorem paperGroupFactorUnitaryTwo_apply
    (ξ : GroupL2 PaperGroupTwo) (h : H) :
    paperGroupFactorUnitaryTwo ξ h =
      paperFourierCoordinateUnitary (semidirectFubini paperThetaTwoHom ξ h) := rfl

/- Kernel translations become the concrete crossed-base multipliers for the
first Zhou factor. Paper: §3. -/
theorem paperGroupFactorUnitaryOne_conj_inl (d : D) :
    paperGroupFactorUnitaryOne.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupOne) :
          GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) =
      crossedKernelMultiplier d := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := paperGroupFactorUnitaryOne.surjective η
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    paperGroupFactorUnitaryOne.symm_apply_apply]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaOneHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupOne) :
            GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionOne
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaOneHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaOneHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupOne) :
              GroupL2 PaperGroupOne →L[ℂ] GroupL2 PaperGroupOne) ξ) h =
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
theorem paperGroupFactorUnitaryTwo_conj_inl (d : D) :
    paperGroupFactorUnitaryTwo.conjStarAlgEquiv
      (leftRegularUnitary
        (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupTwo) :
          GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) =
      crossedMultiplier paperHaarActionTwo (coordinateCharacterCoefficient d) := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := paperGroupFactorUnitaryTwo.surjective η
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    paperGroupFactorUnitaryTwo.symm_apply_apply]
  apply lp.ext
  funext h
  change paperFourierCoordinateUnitary
      (semidirectFubini paperThetaTwoHom
        ((leftRegularUnitary
          (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupTwo) :
            GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo)
          ξ) h) =
    crossedBaseMultiplier paperHaarActionTwo
      (coordinateCharacterCoefficient d)
      (paperFourierCoordinateUnitary
        (semidirectFubini paperThetaTwoHom
          ξ h))
  have hfiber :
      semidirectFubini paperThetaTwoHom
          ((leftRegularUnitary
            (SemidirectProduct.inl (Multiplicative.ofAdd d) : PaperGroupTwo) :
              GroupL2 PaperGroupTwo →L[ℂ] GroupL2 PaperGroupTwo) ξ) h =
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
