/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Zhou-oriented split of the public OpenAI quadratic-tensor proof block
(`ConnesRigidity.lean:661-727`). The source proof terms are preserved after
changing the carrier to Zhou's characteristic-two `V`; this file keeps the
symmetric tensor construction separate from the still-open group actions.
-/
import Connes.Construction

namespace Connes
namespace Construction
namespace SymmetricTensor

/-- Tensor square carrier for the symmetric-data module. Paper: §2. -/
abbrev Tensor := TensorProduct k V V

/-- Pure tensor square. Paper: §2. -/
def square (v : V) : Tensor := v ⊗ₜ[k] v

/-- Symmetric tensor-data submodule. Paper: §2. -/
def Data : Submodule k Tensor := Submodule.span k (Set.range square)

/-- Characteristic-two square vanishes at zero. Paper: §2. -/
@[simp] theorem square_zero : square 0 = 0 := by
  simp only [square, TensorProduct.tmul_zero]

/-- Polarization expansion of a tensor square. Paper: §2. -/
theorem square_add (u v : V) :
    square (u + v) = square u + square v +
      (u ⊗ₜ[k] v + v ⊗ₜ[k] u) := by
  simp only [square, TensorProduct.add_tmul, TensorProduct.tmul_add]
  ac_rfl

/-- Every tensor square belongs to the symmetric-data submodule. Paper: §2. -/
theorem square_mem (v : V) : square v ∈ Data := by
  exact Submodule.subset_span ⟨v, rfl⟩

/-- Diagonal symmetric data. Paper: §2. -/
def diagonal (v : V) : Data := ⟨square v, square_mem v⟩

/-- Underlying tensor of diagonal data. Paper: §2. -/
@[simp] theorem diagonal_val (v : V) : (diagonal v : Tensor) = square v := rfl

/-- Symmetric pure tensors lie in the data submodule. Paper: §2. -/
theorem symmetric_tmul_mem (u v : V) :
    u ⊗ₜ[k] v + v ⊗ₜ[k] u ∈ Data := by
  have h := Data.sub_mem (Data.sub_mem (square_mem (u + v)) (square_mem u))
    (square_mem v)
  rw [square_add] at h
  simpa only [add_assoc, add_sub_cancel_left] using h

/-- Polarization data. Paper: §2. -/
def polarization (u v : V) : Data :=
  ⟨u ⊗ₜ[k] v + v ⊗ₜ[k] u, symmetric_tmul_mem u v⟩

/-- Underlying tensor of polarization data. Paper: §2. -/
@[simp] theorem polarization_val (u v : V) :
    (polarization u v : Tensor) = u ⊗ₜ[k] v + v ⊗ₜ[k] u := rfl

/-- Diagonal polarization identity. Paper: §2. -/
theorem diagonal_add (u v : V) :
    diagonal (u + v) = diagonal u + diagonal v + polarization u v := by
  apply Subtype.ext
  exact square_add u v

/-- Every module over the characteristic-two field is additive exponent two. Paper: §2. -/
theorem add_self_eq_zero {M : Type*} [AddCommGroup M] [Module k M]
    (x : M) : x + x = 0 := by
  calc
    x + x = ((1 : k) + 1) • x := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : k) + 1 = 0 by decide, zero_smul]

/-- Symmetric data has additive exponent two. Paper: §2. -/
theorem data_add_self (d : Data) : d + d = 0 := add_self_eq_zero d

end SymmetricTensor
end Construction
end Connes
