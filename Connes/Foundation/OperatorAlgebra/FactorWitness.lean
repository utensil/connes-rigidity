/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 35621-35749.
Modifications: renamed and generalized the spatial witness while preserving
the spatial-to-tracial argument. Paper: §3. See docs/PORT_MAP.md.
-/
import Mathlib
import Connes.Core

set_option maxHeartbeats 800000

namespace Connes
namespace FactorWitness

noncomputable section

/-- Spatial witness data for a factor equivalence. Paper: §3. -/
structure SpatialWitness (G H : CountableDiscreteGroup) where
  unitary : GroupL2 G ≃ₗᵢ[ℂ] GroupL2 H
  maps_group_factor :
    ∀ T : GroupL2 G →L[ℂ] GroupL2 G,
      T ∈ groupVonNeumannAlgebra G ↔
        unitary.conjStarAlgEquiv T ∈ groupVonNeumannAlgebra H
  maps_vacuum : unitary (delta G 1) = delta H 1

namespace SpatialWitness

universe u v

variable {G : CountableDiscreteGroup.{u}}
variable {H : CountableDiscreteGroup.{v}}

/-- Turn a spatial witness into its conjugation star-algebra equivalence. Paper: §3. -/
def toStarAlgEquiv (w : SpatialWitness G H) :
    GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H where
  toFun x :=
    ⟨w.unitary.conjStarAlgEquiv x,
      (w.maps_group_factor x).mp x.property⟩
  invFun y :=
    ⟨w.unitary.conjStarAlgEquiv.symm y, by
      apply (w.maps_group_factor (w.unitary.conjStarAlgEquiv.symm y)).mpr
      have h := w.unitary.conjStarAlgEquiv.apply_symm_apply
        (y : GroupL2 H →L[ℂ] GroupL2 H)
      rw [h]
      exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact w.unitary.conjStarAlgEquiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact w.unitary.conjStarAlgEquiv.apply_symm_apply y
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_add' x y := by
    apply Subtype.ext
    exact map_add w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
      (y : GroupL2 G →L[ℂ] GroupL2 G)
  map_star' x := by
    apply Subtype.ext
    exact map_star w.unitary.conjStarAlgEquiv
      (x : GroupL2 G →L[ℂ] GroupL2 G)
  map_smul' c x := by
    apply Subtype.ext
    change
      w.unitary.conjStarAlgEquiv
        (c • (x : GroupL2 G →L[ℂ] GroupL2 G)) =
        c • w.unitary.conjStarAlgEquiv
          (x : GroupL2 G →L[ℂ] GroupL2 G)
    exact map_smul w.unitary.conjStarAlgEquiv c
      (x : GroupL2 G →L[ℂ] GroupL2 G)

/-- Mathlib's operator order agrees with the algebraic projection order. -/
private theorem projection_le_iff_mul_eq_left
    {K : CountableDiscreteGroup.{u}}
    {p q : GroupVonNeumannAlgebra K}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    p ≤ q ↔ p * q = p := by
  have hp' : IsStarProjection (p : GroupL2 K →L[ℂ] GroupL2 K) :=
    hp.map (groupVonNeumannAlgebra K).toStarSubalgebra.subtype
  have hq' : IsStarProjection (q : GroupL2 K →L[ℂ] GroupL2 K) :=
    hq.map (groupVonNeumannAlgebra K).toStarSubalgebra.subtype
  rw [show p ≤ q ↔ (p : GroupL2 K →L[ℂ] GroupL2 K) ≤ q from Iff.rfl]
  rw [hp'.le_iff_mul_eq_left hq']
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩

/-- A star-algebra equivalence preserves Mathlib's order between projections. -/
private theorem starAlgEquiv_le_iff
    {K : CountableDiscreteGroup.{u}} {L : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra K ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra L)
    {p q : GroupVonNeumannAlgebra K}
    (hp : IsStarProjection p) (hq : IsStarProjection q) :
    e p ≤ e q ↔ p ≤ q := by
  rw [projection_le_iff_mul_eq_left (hp.map e) (hq.map e),
    projection_le_iff_mul_eq_left hp hq]
  exact ⟨fun h ↦ by
      simpa only [map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h,
    fun h ↦ by simpa only [map_mul] using congrArg e h⟩

/-- A star-algebra equivalence carries a projection supremum to its image. -/
private theorem starAlgEquiv_preservesProjectionSupremum
    {K : CountableDiscreteGroup.{u}} {L : CountableDiscreteGroup.{v}}
    (e : GroupVonNeumannAlgebra K ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra L)
    {S : Set (GroupVonNeumannAlgebra K)} {p : GroupVonNeumannAlgebra K}
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine ⟨hp.1.map e, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hp.2.1 q hq).1.map e,
      (starAlgEquiv_le_iff e (hp.2.1 q hq).1 hp.1).2 (hp.2.1 q hq).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, q ≤ e.symm r := by
      intro q hq
      have h := hupper (e q) ⟨q, hq, rfl⟩
      simpa only [StarAlgEquiv.symm_apply_apply] using
        (starAlgEquiv_le_iff e.symm ((hp.2.1 q hq).1.map e) hr).2 h
    have h := hp.2.2 (e.symm r) hr' hbound
    have h' : e.symm (e p) ≤ e.symm r := by
      simpa only [StarAlgEquiv.symm_apply_apply] using h
    exact (starAlgEquiv_le_iff e.symm (hp.1.map e) hr).1 h'

/-- The conjugation equivalence preserves the projection-supremum relation. Paper: §3. -/
private theorem starAlgEquiv_isNormal
    (e : GroupVonNeumannAlgebra G ≃⋆ₐ[ℂ] GroupVonNeumannAlgebra H) :
    IsNormalStarAlgEquiv e :=
  ⟨fun _ _ ↦ starAlgEquiv_preservesProjectionSupremum e,
    fun _ _ ↦ starAlgEquiv_preservesProjectionSupremum e.symm⟩

/-- The spatial witness preserves the canonical vacuum trace. Paper: §3. -/
theorem trace_preserving (w : SpatialWitness G H)
    (x : GroupVonNeumannAlgebra G) :
    canonicalTrace H (w.toStarAlgEquiv x) = canonicalTrace G x := by
  change inner ℂ (delta H 1)
      (w.unitary ((x : GroupL2 G →L[ℂ] GroupL2 G)
        (w.unitary.symm (delta H 1)))) =
    inner ℂ (delta G 1)
      ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))
  rw [← w.maps_vacuum, w.unitary.symm_apply_apply]
  exact w.unitary.inner_map_map (delta G 1)
    ((x : GroupL2 G →L[ℂ] GroupL2 G) (delta G 1))

/-- Package the spatial witness as a trace-preserving factor equivalence. Paper: §3. -/
def toTracialGroupFactorEquiv
    (w : SpatialWitness G H) : TracialGroupFactorEquiv G H where
  toStarAlgEquiv := w.toStarAlgEquiv
  normal := starAlgEquiv_isNormal w.toStarAlgEquiv
  trace_preserving := w.trace_preserving

end SpatialWitness

/-- Spatial-to-tracial transfer. Paper: §3. -/
theorem tracialEquiv_of_spatialWitness {G H : CountableDiscreteGroup}
    (w : SpatialWitness G H) : TracialGroupFactorsIsomorphic G H :=
  ⟨w.toTracialGroupFactorEquiv⟩

end
end FactorWitness
end Connes
