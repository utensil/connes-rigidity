/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Algebraic part of Zhou §3 for the actual tensor kernel. The old
`FactorIsomorphism` file remains a compatibility layer for the retired
placeholder carrier; this file is the paper-facing target.
-/
import Connes.Construction.PaperActionInstances
import Connes.Foundation.OperatorAlgebra.FactorWitness

namespace Connes
namespace PaperFactorIsomorphism

open MeasureTheory

noncomputable section

abbrev k := Construction.k
abbrev A := Construction.A
abbrev PaperV := Construction.PaperKernel.PaperV
abbrev SymplecticIndex := OpenAIPort.SymplecticIndex
abbrev C := Construction.PaperKernel.C
abbrev TensorAA := Construction.PaperKernel.TensorAA
abbrev H := Construction.H
abbrev ActionData := Construction.PaperKernel.ActionData

/-- The algebraic dual coordinates used by Zhou's fiber model. Paper: §3. -/
abbrev DualCoordinates :=
  (A →ₗ[k] PaperV) × (C →ₗ[k] k)

/-- One finite coordinate of a map `A → V`. Paper: §3. -/
def coordinate (z : A →ₗ[k] PaperV) (i : SymplecticIndex) : A →ₗ[k] k where
  toFun a := z a i
  map_add' a b := by simp
  map_smul' r a := by simp

/-- Bilinear evaluation on a pure tensor. Paper: §3. -/
def tensorFunctional (f g : A →ₗ[k] k) : TensorAA →ₗ[k] k :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => f a * g b
          map_add' := by
            intro b c
            simp [mul_add]
          map_smul' := by
            intro r b
            simp [smul_eq_mul]
            ring }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        simp [add_mul]
      map_smul' := by
        intro r a
        apply LinearMap.ext
        intro b
        simp [smul_eq_mul, mul_assoc] }

/-- Restriction of tensor evaluation to the flip-fixed carrier. Paper: §3. -/
def tensorFunctionalOnC (f g : A →ₗ[k] k) : C →ₗ[k] k :=
  (tensorFunctional f g).domRestrict C

@[simp] theorem tensorFunctionalOnC_diagonal
    (f g : A →ₗ[k] k) (a : A) :
    tensorFunctionalOnC f g (Construction.PaperKernel.diagonal a) =
      f a * g a := by
  simp [tensorFunctionalOnC, tensorFunctional,
    Construction.PaperKernel.diagonal]

/-- Zhou's quadratic functional on the symmetric tensor dual. Paper: §3. -/
def quadraticMap (z : A →ₗ[k] PaperV) : C →ₗ[k] k :=
  tensorFunctionalOnC (coordinate z (Sum.inl 0)) (coordinate z (Sum.inr 0)) +
    tensorFunctionalOnC (coordinate z (Sum.inl 1)) (coordinate z (Sum.inr 1))

@[simp] theorem quadraticMap_diagonal (z : A →ₗ[k] PaperV) (a : A) :
    quadraticMap z (Construction.PaperKernel.diagonal a) =
      OpenAIPort.standardQuadraticForm (z a) := by
  simp [quadraticMap, coordinate, OpenAIPort.standardQuadraticForm]

/-- The nontrivial fiber shear from Zhou Proposition 3.2. Paper: §3. -/
def fiberShear : DualCoordinates → DualCoordinates := fun p =>
  (p.1, p.2 + quadraticMap p.1)

/-- The characteristic-two cancellation behind the fiber shear. Paper: §3. -/
theorem fiberShear_involutive (p : DualCoordinates) :
    fiberShear (fiberShear p) = p := by
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro c
    change (p.2 c + quadraticMap p.1 c) + quadraticMap p.1 c = p.2 c
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Data needed to turn Zhou's algebraic shear into the analytic factor map.
The measure, action conjugacy, and spatial implementation are explicit inputs
because the current repository does not model the paper's locally compact
dual/Haar construction. Paper: §§3, 3.4. -/
structure PaperFactorData [MeasurableSpace DualCoordinates]
    (actions : ActionData) where
  measure : MeasureTheory.Measure DualCoordinates
  actionOne : H →* Equiv.Perm DualCoordinates
  actionTwo : H →* Equiv.Perm DualCoordinates
  measurable_shear : Measurable fiberShear
  measure_preserving : MeasurePreserving fiberShear measure measure
  conjugates : ∀ h : H,
    fiberShear ∘ (actionOne h : DualCoordinates → DualCoordinates) =
      (actionTwo h : DualCoordinates → DualCoordinates) ∘ fiberShear
  spatialWitness :
    FactorWitness.SpatialWitness
      (Construction.PaperKernel.paperGammaOneOf actions)
      (Construction.PaperKernel.paperGammaTwoOf actions)

/-- The algebraic shear preserves the supplied Haar witness. Paper: §3. -/
theorem fiberShear_preservesHaar
    [MeasurableSpace DualCoordinates] {actions : ActionData}
    (data : PaperFactorData actions) :
    MeasurePreserving fiberShear data.measure data.measure :=
  data.measure_preserving

/-- The algebraic shear conjugates the two supplied dual actions. Paper: §3. -/
theorem fiberShear_conjugates_actions
    [MeasurableSpace DualCoordinates] {actions : ActionData}
    (data : PaperFactorData actions) (h : H) :
    fiberShear ∘ (data.actionOne h : DualCoordinates → DualCoordinates) =
      (data.actionTwo h : DualCoordinates → DualCoordinates) ∘ fiberShear :=
  data.conjugates h

/-- The paper-shaped factor-isomorphism conclusion from an analytic witness.
The generic spatial-to-tracial transfer is proved in the local foundation.
Paper: §3. -/
theorem groupFactors_isomorphic
    [MeasurableSpace DualCoordinates] {actions : ActionData}
    (data : PaperFactorData actions) :
    TracialGroupFactorsIsomorphic
      (Construction.PaperKernel.paperGammaOneOf actions)
      (Construction.PaperKernel.paperGammaTwoOf actions) :=
  FactorWitness.tracialEquiv_of_spatialWitness data.spatialWitness

end
end PaperFactorIsomorphism
end Connes
