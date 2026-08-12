/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The concrete §3 factor-data assembly from the proved spatial crossed-product
witness. Paper: §3.
-/
import Connes.PaperFactorIsomorphism
import Connes.Foundation.OperatorAlgebra.PaperFactorClosure

namespace Connes
namespace PaperConcreteFactor

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualTopology
open PaperDualShearMeasure
open PaperFactorIsomorphism
open PaperFactorClosure

noncomputable section

abbrev H := Construction.H
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates
/- Package the actual paper coordinates, Haar measure, and conjugate actions.
Paper: §3. -/
def paperFactorData : PaperFactorData PaperKernel.paperActionData where
  measure := coordinatesHaar
  actionOne := paperCoordinatePermActionOne
  actionTwo := paperCoordinatePermActionTwo
  measurable_shear := measurable_fiberShear
  measure_preserving := fiberShear_measurePreserving
  conjugates := by
    intro h
    apply funext
    intro p
    change fiberShear (paperCoordinateActionOne h p) =
      paperCoordinateActionTwo h (fiberShear p)
    exact PaperDualActionConjugacy.paperFiberShear_conjugates_paperActions h p
  spatialWitness := paperSpatialWitness

/- The concrete paper factors are trace-preservingly isomorphic. Paper: §3. -/
theorem groupFactors_isomorphic :
    TracialGroupFactorsIsomorphic
      (paperGammaOneOf PaperKernel.paperActionData)
      (paperGammaTwoOf PaperKernel.paperActionData) :=
  PaperFactorIsomorphism.groupFactors_isomorphic paperFactorData

end
end PaperConcreteFactor
end Connes
