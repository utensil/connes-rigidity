/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete normalized-Haar actions and the Zhou fiber-shear equivalence for the
crossed-product model. Paper: §3.
-/
import Connes.Foundation.OperatorAlgebra.PaperCrossedAction
import Connes.Foundation.OperatorAlgebra.PaperDualActionConjugacy

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace PaperCrossedHaar

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualTopology
open PaperFactorIsomorphism
open PaperDualShearMeasure
open PaperCrossedAction
open CrossedProduct

noncomputable section

abbrev H := Construction.H
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates

/- The inverse of each coordinate action is the action of the inverse group
element. Paper: §3. -/
theorem paperCoordinateActionOne_symm (h : H) :
    (paperCoordinateActionOne h).symm = paperCoordinateActionOne h⁻¹ := by
  apply AddEquiv.ext
  intro p
  apply (paperCoordinateActionOne h).injective
  simpa [coordinateAction_one, AddEquiv.trans_apply] using
    congrArg (fun e : Coordinates ≃+ Coordinates => e p)
      (coordinateAction_mul paperDualActionOne h h⁻¹)

/- The second coordinate action has the same inverse formula. Paper: §3. -/
theorem paperCoordinateActionTwo_symm (h : H) :
    (paperCoordinateActionTwo h).symm = paperCoordinateActionTwo h⁻¹ := by
  apply AddEquiv.ext
  intro p
  apply (paperCoordinateActionTwo h).injective
  simpa [coordinateAction_one, AddEquiv.trans_apply] using
    congrArg (fun e : Coordinates ≃+ Coordinates => e p)
      (coordinateAction_mul paperDualActionTwo h h⁻¹)

/- The first concrete action preserves Zhou's normalized coordinate Haar
measure. Paper: §3. -/
theorem paperCoordinateActionOne_measurePreserving (h : H) :
    MeasurePreserving (paperCoordinateActionOne h : Coordinates → Coordinates)
      coordinatesHaar coordinatesHaar := by
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_preserving_addEquiv
    Coordinates (paperCoordinateActionOne h)
    (continuous_paperCoordinateActionOne h) (by
      rw [paperCoordinateActionOne_symm]
      exact continuous_paperCoordinateActionOne h⁻¹)

/- The second concrete action preserves Zhou's normalized coordinate Haar
measure. Paper: §3. -/
theorem paperCoordinateActionTwo_measurePreserving (h : H) :
    MeasurePreserving (paperCoordinateActionTwo h : Coordinates → Coordinates)
      coordinatesHaar coordinatesHaar := by
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_preserving_addEquiv
    Coordinates (paperCoordinateActionTwo h)
    (continuous_paperCoordinateActionTwo h) (by
      rw [paperCoordinateActionTwo_symm]
      exact continuous_paperCoordinateActionTwo h⁻¹)

/- The first Zhou action packaged as a probability Haar action. Paper: §3. -/
def paperHaarActionOne : HaarProbabilityAction H Coordinates where
  measure := coordinatesHaar
  haar := by
    unfold coordinatesHaar
    infer_instance
  probability := by
    unfold coordinatesHaar
    infer_instance
  action := paperCoordinatePermActionOne
  action_add := by
    intro h z z'
    change paperCoordinateActionOne h (z + z') =
      paperCoordinateActionOne h z + paperCoordinateActionOne h z'
    exact (paperCoordinateActionOne h).map_add z z'
  action_preserves_measure := paperCoordinateActionOne_measurePreserving

/- The second Zhou action packaged as a probability Haar action. Paper: §3. -/
def paperHaarActionTwo : HaarProbabilityAction H Coordinates where
  measure := coordinatesHaar
  haar := by
    unfold coordinatesHaar
    infer_instance
  probability := by
    unfold coordinatesHaar
    infer_instance
  action := paperCoordinatePermActionTwo
  action_add := by
    intro h z z'
    change paperCoordinateActionTwo h (z + z') =
      paperCoordinateActionTwo h z + paperCoordinateActionTwo h z'
    exact (paperCoordinateActionTwo h).map_add z z'
  action_preserves_measure := paperCoordinateActionTwo_measurePreserving

/- The quadratic fiber shear as a measurable involutive equivalence. Paper: §3. -/
def paperFiberShearMeasurableEquiv : Coordinates ≃ᵐ Coordinates where
  toEquiv :=
    { toFun := fiberShear
      invFun := fiberShear
      left_inv := fiberShear_involutive
      right_inv := fiberShear_involutive }
  measurable_toFun := measurable_fiberShear
  measurable_invFun := measurable_fiberShear

/- Zhou's fiber shear is an equivariant Haar equivalence between the two
crossed-product bases. Paper: §3. -/
def paperHaarEquiv :
    EquivariantHaarEquiv paperHaarActionOne paperHaarActionTwo where
  toMeasurableEquiv := paperFiberShearMeasurableEquiv
  measure_preserving := fiberShear_measurePreserving
  equivariant := by
    intro h p
    change fiberShear (paperCoordinateActionOne h p) =
      paperCoordinateActionTwo h (fiberShear p)
    exact PaperDualActionConjugacy.paperFiberShear_conjugates_paperActions h p

end
end PaperCrossedHaar
end Connes
