/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Mechanical transfer of the unitary/linear-isometry bridge from
OpenAI/ten-proofs, `ConnesRigidity.lean:304-348`, into the Zhou-oriented
operator-algebra directory. The source is public Apache-2.0 code; this file
keeps the proof terms and changes only the namespace and import boundary.
-/
import Connes.Core

namespace Connes
namespace OpenAIPort

universe u

noncomputable def unitaryLinearIsometryEquiv
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : unitary (H →L[ℂ] H)) :
    H ≃ₗᵢ[ℂ] H where
  toFun := U
  invFun := ((U⁻¹ : unitary (H →L[ℂ] H)) : H →L[ℂ] H)
  left_inv x := by
    change (↑(U⁻¹ * U) : H →L[ℂ] H) x = x
    simp only [inv_mul_cancel, OneMemClass.coe_one, one_apply_eq_self]
  right_inv x := by
    change (↑(U * U⁻¹) : H →L[ℂ] H) x = x
    simp only [mul_inv_cancel, OneMemClass.coe_one, one_apply_eq_self]
  map_add' x y := map_add (U : H →L[ℂ] H) x y
  map_smul' c x := map_smul (U : H →L[ℂ] H) c x
  norm_map' := ContinuousLinearMap.norm_map_of_mem_unitary U.property

/-- The pointwise action of the transferred unitary is unchanged. Paper: §3. -/
@[simp] theorem unitaryLinearIsometryEquiv_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : unitary (H →L[ℂ] H)) (x : H) :
    unitaryLinearIsometryEquiv U x = (U : H →L[ℂ] H) x :=
  rfl

noncomputable def linearIsometryEquivUnitary
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H ≃ₗᵢ[ℂ] H) :
    unitary (H →L[ℂ] H) :=
  ⟨(e : H →L[ℂ] H), by
    rw [Unitary.mem_iff, e.star_eq_symm]
    constructor <;> ext x <;> simp⟩

/-- The unitary wrapper evaluates to the supplied linear isometry. Paper: §3. -/
@[simp] theorem linearIsometryEquivUnitary_apply
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e : H ≃ₗᵢ[ℂ] H) (x : H) :
    (linearIsometryEquivUnitary e : H →L[ℂ] H) x = e x :=
  rfl

end OpenAIPort
end Connes
