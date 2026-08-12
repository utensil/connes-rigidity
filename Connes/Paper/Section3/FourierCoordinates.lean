/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Fourier transport from Zhou's actual compact dual to the raw coordinate Haar
model. This is the kernel part of the §3 crossed-product bridge. Paper: §3.
-/
import Connes.Paper.Section3.FourierAction
import Connes.Paper.Section3.DualShearMeasure

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace PaperFourierCoordinates

open MeasureTheory
open Construction
open Construction.PaperKernel
open PaperDualHaar
open PaperDualTopology
open PaperFactorIsomorphism
open PaperFourier
open PaperFourierAction

noncomputable section

abbrev D := PaperKernel.D
abbrev CharacterSpace := PaperDualHaar.PaperCharacterSpace
abbrev Coordinates := PaperFactorIsomorphism.DualCoordinates
abbrev CharacterL2 := Lp ℂ 2 paperCharacterHaar
abbrev CoordinateL2 := Lp ℂ 2 coordinatesHaar

local instance paperDDecidableEq : DecidableEq D := Classical.decEq D
local instance paperMultiplicativeDDecidableEq :
    DecidableEq (Multiplicative D) := Classical.decEq _

/- The algebraic coordinate equivalence with its Borel inverse. Paper: §3. -/
def characterCoordinatesMeasurableEquiv : CharacterSpace ≃ᵐ Coordinates where
  toEquiv := PaperDualHaar.characterCoordinatesEquiv.toEquiv
  measurable_toFun := characterCoordinatesHomeomorph.continuous.measurable
  measurable_invFun := characterCoordinatesHomeomorph.symm.continuous.measurable

/- Transport of normalized Haar from the compact dual to Zhou coordinates.
Paper: §3. -/
theorem characterCoordinates_measurePreserving :
    MeasurePreserving characterCoordinatesMeasurableEquiv
      paperCharacterHaar coordinatesHaar := by
  let μ := paperCharacterHaar
  letI : Measure.IsAddHaarMeasure μ := by
    dsimp [μ, paperCharacterHaar]
    infer_instance
  haveI : Measure.IsAddHaarMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    AddEquiv.isAddHaarMeasure_map μ PaperDualHaar.characterCoordinatesEquiv
      characterCoordinatesHomeomorph.continuous
      characterCoordinatesHomeomorph.symm.continuous
  haveI : IsProbabilityMeasure
      (Measure.map characterCoordinatesMeasurableEquiv μ) :=
    μ.isProbabilityMeasure_map
      characterCoordinatesHomeomorph.continuous.measurable.aemeasurable
  refine ⟨characterCoordinatesMeasurableEquiv.measurable, ?_⟩
  change Measure.map characterCoordinatesMeasurableEquiv μ = coordinatesHaar
  unfold coordinatesHaar
  exact NormalizedHaar.normalizedAddHaar_unique Coordinates
    (Measure.map characterCoordinatesMeasurableEquiv μ)

/- The L² pullback along the character/coordinate equivalence. Paper: §3. -/
def characterCoordinatesLpEquiv : CharacterL2 ≃ₗᵢ[ℂ] CoordinateL2 where
  toLinearEquiv :=
    { toFun := Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving)
      invFun := Lp.compMeasurePreserving
        characterCoordinatesMeasurableEquiv characterCoordinates_measurePreserving
      left_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
          characterCoordinates_measurePreserving
        simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply,
          show (fun z : CharacterSpace ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      right_inv := by
        intro f
        have h := Lp.compMeasurePreserving_comp_apply f
          characterCoordinates_measurePreserving
          (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
            characterCoordinates_measurePreserving)
        simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
          show (fun z : Coordinates ↦ z) = id from rfl,
          Lp.compMeasurePreserving_id, AddMonoidHom.id_apply] using h.symm
      map_add' := by
        intro f g
        exact map_add
          (Lp.compMeasurePreserving
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) f g
      map_smul' := by
        intro c f
        exact map_smul
          (Lp.compMeasurePreservingₗ ℂ
            (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
            (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
              characterCoordinates_measurePreserving)) c f }
  norm_map' := fun f => Lp.norm_compMeasurePreserving f
    (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
      characterCoordinates_measurePreserving)

@[simp] theorem characterCoordinatesLpEquiv_apply (f : CharacterL2) :
    characterCoordinatesLpEquiv f =
      Lp.compMeasurePreserving
        (characterCoordinatesMeasurableEquiv.symm : Coordinates → CharacterSpace)
        (MeasurePreserving.symm characterCoordinatesMeasurableEquiv
          characterCoordinates_measurePreserving) f := rfl

/- The paper Fourier transform with target in Zhou coordinates. Paper: §3. -/
def paperFourierCoordinateUnitary :
    GroupL2 (Multiplicative D) ≃ₗᵢ[ℂ] CoordinateL2 :=
  paperFourierUnitary.trans characterCoordinatesLpEquiv

def coordinateCharacterL2 (d : D) : CoordinateL2 :=
  characterCoordinatesLpEquiv (characterL2 d)

@[simp] theorem paperFourierCoordinateUnitary_single (d : D) :
    paperFourierCoordinateUnitary
        (lp.single 2 (Multiplicative.ofAdd d) (1 : ℂ)) =
      coordinateCharacterL2 d := by
  exact congrArg characterCoordinatesLpEquiv
    (paperFourierUnitary_single d)

/- The transported kernel multiplier in raw coordinates. Paper: §3. -/
def coordinateCharacterMultiplier (d : D) :
    CoordinateL2 →L[ℂ] CoordinateL2 :=
  characterCoordinatesLpEquiv.conjStarAlgEquiv
    (characterMultiplier (complexCharacter d))

/- Kernel regular translations become the transported Zhou-coordinate
multiplier. Paper: §3. -/
theorem paperFourierCoordinate_conjugates_regular (d : D) :
    paperFourierCoordinateUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)) =
      coordinateCharacterMultiplier d := by
  change (characterCoordinatesLpEquiv.conjStarAlgEquiv
      (paperFourierUnitary.conjStarAlgEquiv
        (leftRegularUnitary (Multiplicative.ofAdd d) :
          GroupL2 (Multiplicative D) →L[ℂ]
            GroupL2 (Multiplicative D)))) = _
  rw [paperFourier_conjugates_regular]
  rfl

end
end PaperFourierCoordinates
end Connes
