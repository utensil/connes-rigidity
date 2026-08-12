/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Invariant dual-measure transport for Zhou's finite chart detector. Paper: §4.
-/
import Connes.Foundation.LinearAlgebra.PaperChartDetector
import Connes.Foundation.LinearAlgebra.PaperChartOrbits
import Connes.Foundation.OperatorAlgebra.NormalizedHaar
import Connes.Foundation.OperatorAlgebra.PaperDualTopology
import Connes.Foundation.OperatorAlgebra.PaperDualShearMeasure
import Connes.Foundation.OperatorAlgebra.SpectralCriterion

set_option maxHeartbeats 1600000

namespace Connes
namespace PaperChartMeasure

open MeasureTheory
open Construction
open Construction.PaperKernel
open BinaryPontryaginDual
open PaperDualHaar
open PaperDualTopology

noncomputable section

abbrev k := Construction.k
abbrev D := PaperKernel.D
abbrev CharacterSpace := PaperDualTopology.CharacterSpace

def continuousMulAut (e : AddAut D) :
    Multiplicative D →ₜ* Multiplicative D where
  toFun x := Multiplicative.ofAdd (e x.toAdd)
  map_one' := by simp
  map_mul' x y := by simp [map_add]
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem continuousMulAut_apply (e : AddAut D) (x : Multiplicative D) :
    continuousMulAut e x = Multiplicative.ofAdd (e x.toAdd) := rfl

/- The dual automorphism is precomposition by the inverse kernel
automorphism. Paper: §4. -/
def dualCharacterEquiv (e : AddAut D) : CharacterSpace ≃+ CharacterSpace where
  toFun χ := Additive.ofMul
    (PontryaginDual.map (continuousMulAut e.symm) (Additive.toMul χ))
  invFun χ := Additive.ofMul
    (PontryaginDual.map (continuousMulAut e) (Additive.toMul χ))
  left_inv χ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (PontryaginDual.map (continuousMulAut e)
      (PontryaginDual.map (continuousMulAut e.symm)
        (Additive.toMul χ))) x = (Additive.toMul χ) x
    rw [PontryaginDual.map_apply, PontryaginDual.map_apply]
    rw [continuousMulAut_apply, continuousMulAut_apply]
    simp
  right_inv χ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    change (PontryaginDual.map (continuousMulAut e.symm)
      (PontryaginDual.map (continuousMulAut e)
        (Additive.toMul χ))) x = (Additive.toMul χ) x
    rw [PontryaginDual.map_apply, PontryaginDual.map_apply]
    rw [continuousMulAut_apply, continuousMulAut_apply]
    simp
  map_add' χ ψ := by
    apply Additive.toMul.injective
    apply PontryaginDual.ext
    intro x
    simp [PontryaginDual.map, continuousMulAut]

@[simp] theorem dualCharacterEquiv_apply (e : AddAut D) (χ : CharacterSpace)
    (x : D) :
    (Additive.toMul (dualCharacterEquiv e χ))
        (Multiplicative.ofAdd x) =
      (Additive.toMul χ) (Multiplicative.ofAdd (e.symm x)) := by
  rfl

theorem dualCharacterEquiv_continuous (e : AddAut D) :
    Continuous (dualCharacterEquiv e) := by
  change Continuous (PontryaginDual.map (continuousMulAut e.symm))
  exact (PontryaginDual.map (continuousMulAut e.symm)).continuous_toFun

theorem dualCharacterEquiv_symm_continuous (e : AddAut D) :
    Continuous (dualCharacterEquiv e).symm := by
  change Continuous (PontryaginDual.map (continuousMulAut e))
  exact (PontryaginDual.map (continuousMulAut e)).continuous_toFun

theorem dualCharacterEquiv_measurePreserving (e : AddAut D) :
    MeasurePreserving (dualCharacterEquiv e)
      PaperDualHaar.paperCharacterHaar PaperDualHaar.paperCharacterHaar := by
  simpa [PaperDualHaar.paperCharacterHaar] using
    (NormalizedHaar.normalizedAddHaar_preserving_addEquiv
      CharacterSpace (dualCharacterEquiv e)
      (dualCharacterEquiv_continuous e)
      (dualCharacterEquiv_symm_continuous e))

def dualCharacterEquivOfAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    CharacterSpace ≃+ CharacterSpace :=
  dualCharacterEquiv (Multiplicative.toAdd (action h))

/- The paper-facing action is kept on the additive character model. The
existing generic criterion uses the raw Pontryagin-dual model, so this
definition records the same transport without pretending those two types are
definitionally equal. Paper: §4. -/
def paperDualCharacterAction {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D)) (h : H) :
    CharacterSpace → CharacterSpace := dualCharacterEquivOfAction action h

/- Invariant probability measure for the additive character action. Paper: §4. -/
def IsInvariantPaperSpectralMeasure {H : CountableDiscreteGroup}
    (action : H →* Multiplicative (AddAut D))
    (μ : ProbabilityMeasure CharacterSpace) : Prop :=
  ∀ h : H,
    (μ : Measure CharacterSpace).map (paperDualCharacterAction action h) = μ

def linearDetector (d : D) : Set CharacterSpace :=
  {χ | BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul χ) d = 1}

theorem measurableSet_linearDetector (d : D) :
    MeasurableSet (linearDetector d) := by
  exact (PaperDualTopology.continuous_characterLinear_eval d).measurable
    (MeasurableSet.singleton 1)

theorem paperDualCharacterAction_preimage_linearDetector
    {H : CountableDiscreteGroup} (action : H →* Multiplicative (AddAut D))
    (h : H) (d e : D)
    (he : Multiplicative.toAdd (action h⁻¹) e = d) :
    paperDualCharacterAction action h ⁻¹' linearDetector e = linearDetector d := by
  ext χ
  change BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul (paperDualCharacterAction action h χ)) e = 1 ↔
    BinaryPontryaginDual.characterLinear (M := D)
      (Additive.toMul χ) d = 1
  have heval :
      BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul (paperDualCharacterAction action h χ)) e =
        BinaryPontryaginDual.characterLinear (M := D)
          (Additive.toMul χ) d := by
    apply ZMod.injective_toCircle
    rw [BinaryPontryaginDual.characterLinear_circle,
      BinaryPontryaginDual.characterLinear_circle]
    change (Additive.toMul
        (dualCharacterEquiv (Multiplicative.toAdd (action h)) χ))
          (Multiplicative.ofAdd e) =
      (Additive.toMul χ) (Multiplicative.ofAdd d)
    rw [dualCharacterEquiv_apply]
    have haction :
        (Multiplicative.toAdd (action h)).symm e =
          Multiplicative.toAdd (action h⁻¹) e := by
      simp
    rw [haction, he]
  rw [heval]

theorem detector_measure_eq_of_invariant
    {H : CountableDiscreteGroup} (action : H →* Multiplicative (AddAut D))
    (μ : ProbabilityMeasure CharacterSpace)
    (hinv : IsInvariantPaperSpectralMeasure action μ)
    (h : H) (d e : D)
    (he : Multiplicative.toAdd (action h⁻¹) e = d) :
    (μ : Measure CharacterSpace) (linearDetector e) =
      (μ : Measure CharacterSpace) (linearDetector d) := by
  have hmeas : Measurable (paperDualCharacterAction action h) := by
    exact (dualCharacterEquiv_continuous
      (Multiplicative.toAdd (action h))).measurable
  calc
    (μ : Measure CharacterSpace) (linearDetector e) =
        (Measure.map (paperDualCharacterAction action h) μ)
          (linearDetector e) := by rw [hinv h]
    _ = (μ : Measure CharacterSpace)
        (paperDualCharacterAction action h ⁻¹' linearDetector e) := by
      rw [Measure.map_apply hmeas
        (measurableSet_linearDetector e)]
    _ = (μ : Measure CharacterSpace) (linearDetector d) := by
      rw [paperDualCharacterAction_preimage_linearDetector action h d e he]

end
end PaperChartMeasure
end Connes
