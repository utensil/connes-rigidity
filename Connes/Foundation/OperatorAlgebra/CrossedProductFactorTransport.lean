/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Generator and closure transport for the crossed-product model.  This file
separates the generic analytic transport from Zhou's concrete action witness.
The proof pattern follows the public OpenAI/ten-proofs construction.  Paper:
§3.
-/
import Connes.Foundation.OperatorAlgebra.CrossedProductTransport
import Connes.Foundation.OperatorAlgebra.SemidirectClosure

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Connes
namespace CrossedProduct

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

universe u v w

variable {K : Type u} [Group K]
variable {Ω : Type v} [AddCommGroup Ω] [TopologicalSpace Ω] [MeasurableSpace Ω]
variable {Ξ : Type w} [AddCommGroup Ξ] [TopologicalSpace Ξ] [MeasurableSpace Ξ]

/- The base multiplier conjugacy is the pointwise transport theorem lifted to
the crossed Hilbert space. Paper: §3. -/
theorem crossedHaarHilbertEquiv_multiplier_conj
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient X) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv
        (crossedMultiplier X f) =
      crossedMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f) := by
  apply ContinuousLinearMap.ext
  intro η
  obtain ⟨ξ, rfl⟩ := (crossedHaarHilbertEquiv e).surjective η
  apply lp.ext
  funext k
  change
    crossedHaarHilbertEquiv e
      (crossedMultiplier X f
        ((crossedHaarHilbertEquiv e).symm
          ((crossedHaarHilbertEquiv e) ξ))) k =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  rw [LinearIsometryEquiv.symm_apply_apply]
  change
    crossedBaseHaarEquiv e (crossedBaseMultiplier X f (ξ k)) =
      crossedBaseMultiplier Y
        (Lp.compMeasurePreserving e.toMeasurableEquiv.symm
          (EquivariantHaarEquiv.symm e).measure_preserving f)
        (crossedBaseHaarEquiv e (ξ k))
  exact crossedBaseHaarEquiv_multiplier_apply e f (ξ k)

/- The coefficient pullback has the expected inverse. Paper: §3. -/
theorem crossedCoefficient_pullback_symm_apply
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (f : crossedCoefficient Y) :
    Lp.compMeasurePreserving e.toMeasurableEquiv.symm
      (EquivariantHaarEquiv.symm e).measure_preserving
      (Lp.compMeasurePreserving e.toMeasurableEquiv
        e.measure_preserving f) = f := by
  let hs : MeasurePreserving
      (e.toMeasurableEquiv.symm : Ξ → Ω) Y.measure X.measure :=
    (EquivariantHaarEquiv.symm e).measure_preserving
  have h := Lp.compMeasurePreserving_comp_apply f e.measure_preserving hs
  simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply,
    show (fun z : Ξ ↦ z) = id from rfl, Lp.compMeasurePreserving_id,
    AddMonoidHom.id_apply] using h.symm

/- The two crossed-product generator families are transported exactly.
Paper: §3. -/
theorem crossedGeneratorSet_image
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y) :
    (crossedHaarHilbertEquiv e).conjStarAlgEquiv '' crossedGeneratorSet X =
      crossedGeneratorSet Y := by
  ext T
  constructor
  · rintro ⟨S, hS, rfl⟩
    rcases hS with ⟨f, rfl⟩ | ⟨k, rfl⟩
    · exact Or.inl ⟨_, (crossedHaarHilbertEquiv_multiplier_conj e f).symm⟩
    · exact Or.inr ⟨k, (crossedHaarHilbertEquiv_group_conj e k).symm⟩
  · rintro (⟨f, rfl⟩ | ⟨k, rfl⟩)
    · let g : crossedCoefficient X :=
        Lp.compMeasurePreserving e.toMeasurableEquiv
          e.measure_preserving f
      refine ⟨crossedMultiplier X g, Or.inl ⟨g, rfl⟩, ?_⟩
      rw [crossedHaarHilbertEquiv_multiplier_conj]
      congr 1
      exact crossedCoefficient_pullback_symm_apply e f
    · exact ⟨(crossedGroupUnitary X k).toContinuousLinearEquiv.toContinuousLinearMap,
        Or.inr ⟨k, rfl⟩,
        crossedHaarHilbertEquiv_group_conj e k⟩

/- Membership in the generated crossed algebra is invariant under transport.
Paper: §3. -/
theorem crossedHaarHilbertEquiv_mem_algebra_iff
    {X : HaarProbabilityAction K Ω}
    {Y : HaarProbabilityAction K Ξ}
    (e : EquivariantHaarEquiv X Y)
    (T : crossedHilbert X →L[ℂ] crossedHilbert X) :
    T ∈ (crossedProductModel X).algebra ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        (crossedProductModel Y).algebra := by
  change
    T ∈ vonNeumannClosure (crossedGeneratorSet X) ↔
      (crossedHaarHilbertEquiv e).conjStarAlgEquiv T ∈
        vonNeumannClosure (crossedGeneratorSet Y)
  rw [← crossedGeneratorSet_image e]
  exact (mem_vonNeumannClosure_iff_of_conj_image_eq
    (crossedHaarHilbertEquiv e) (crossedGeneratorSet X)
      ((crossedHaarHilbertEquiv e).conjStarAlgEquiv '' crossedGeneratorSet X)
      (by rfl) T)

end
end CrossedProduct
end Connes
