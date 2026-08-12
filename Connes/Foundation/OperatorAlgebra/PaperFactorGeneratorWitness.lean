/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Zhou's concrete factor witness is expressed through the regular generator
transport equations.  This keeps the analytic crossed-product construction
separate from the proved regular-factor reduction.
Paper: §3.
-/
import Connes.Foundation.OperatorAlgebra.PaperFactorGeneratorTransport

namespace Connes
namespace PaperFactorGeneratorWitness

open Construction
open Construction.PaperKernel
open SemidirectGeneratorTransport

noncomputable section

abbrev A := Multiplicative PaperKernel.D
abbrev H := Construction.H
abbrev ActionData := PaperKernel.ActionData

/- The Zhou factor witness data at the generator level. Paper: §3. -/
structure Data (actions : ActionData) where
  unitary : GroupL2 (paperGammaOneOf actions) ≃ₗᵢ[ℂ]
    GroupL2 (paperGammaTwoOf actions)
  kernel_generator : ∀ a : A,
    unitary.conjStarAlgEquiv
        (leftRegularRepresentation (paperGammaOneOf actions)
          (SemidirectProduct.inl a) :
          GroupL2 (paperGammaOneOf actions) →L[ℂ]
            GroupL2 (paperGammaOneOf actions)) =
      (leftRegularRepresentation (paperGammaTwoOf actions)
        (SemidirectProduct.inl a) :
        GroupL2 (paperGammaTwoOf actions) →L[ℂ]
          GroupL2 (paperGammaTwoOf actions))
  quotient_generator : ∀ h : H,
    unitary.conjStarAlgEquiv
        (leftRegularRepresentation (paperGammaOneOf actions)
          (SemidirectProduct.inr h) :
          GroupL2 (paperGammaOneOf actions) →L[ℂ]
            GroupL2 (paperGammaOneOf actions)) =
      (leftRegularRepresentation (paperGammaTwoOf actions)
        (SemidirectProduct.inr h) :
        GroupL2 (paperGammaTwoOf actions) →L[ℂ]
          GroupL2 (paperGammaTwoOf actions))
  maps_vacuum :
    unitary (delta (paperGammaOneOf actions) 1) =
      delta (paperGammaTwoOf actions) 1

/- The paper generator equations instantiate the generic semidirect data.
Paper: §3. -/
def toSemidirectData {actions : ActionData} (data : Data actions) :
    SemidirectGeneratorTransport.Data data.unitary where
  kernel_generator := data.kernel_generator
  quotient_generator := data.quotient_generator

/- The generator-level witness yields the factor witness consumed by Zhou's
factor-isomorphism layer. Paper: §3. -/
def toSpatialWitness {actions : ActionData} (data : Data actions) :
    FactorWitness.SpatialWitness
      (paperGammaOneOf actions) (paperGammaTwoOf actions) where
  unitary := data.unitary
  maps_group_factor := by
    intro T
    exact SemidirectGeneratorTransport.mem_regularClosure_iff
      (toSemidirectData data) T
  maps_vacuum := data.maps_vacuum

/- The generator-level witness is sufficient for the paper-shaped factor
conclusion. Paper: §3. -/
theorem groupFactors_isomorphic {actions : ActionData} (data : Data actions) :
    TracialGroupFactorsIsomorphic
      (paperGammaOneOf actions) (paperGammaTwoOf actions) :=
  FactorWitness.tracialEquiv_of_spatialWitness (toSpatialWitness data)

end
end PaperFactorGeneratorWitness
end Connes
