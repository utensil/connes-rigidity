/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The split-extension decomposition and invariant-vector calculation are adapted
from the public OpenAI/ten-proofs Connes formalization at commit
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6. They are kept generic so the Zhou
spectral proof can later supply the actual kernel and action data.
-/
import Mathlib
import Connes.Core

namespace Connes

universe u

/-- Split abelian extension data for the spectral property-(T) argument. Paper: §4. -/
structure SplitAbelianExtension
    (A : Type u) [AddCommGroup A]
    (G H : CountableDiscreteGroup.{u}) where
  inclusion : Multiplicative A →* G
  quotient : G →* H
  splitting : H →* G
  quotient_splitting : quotient.comp splitting = MonoidHom.id H
  exact : quotient.ker = inclusion.range
  action : H →* Multiplicative (AddAut A)
  conjugation : ∀ (h : H) (a : A),
    splitting h * inclusion (Multiplicative.ofAdd a) * (splitting h)⁻¹ =
      inclusion (Multiplicative.ofAdd
        ((Multiplicative.toAdd (action h)) a))

namespace SplitAbelianExtension

variable {A : Type u} [AddCommGroup A]
variable {G H : CountableDiscreteGroup.{u}}

/-- The split quotient evaluates to the identity on its section. Paper: §4. -/
@[simp] theorem quotient_splitting_apply
    (E : SplitAbelianExtension A G H) (h : H) :
    E.quotient (E.splitting h) = h := by
  have heq := DFunLike.congr_fun E.quotient_splitting h
  exact heq

/-- Every extension element has kernel-section coordinates. Paper: §4. -/
theorem exists_kernel_mul_splitting
    (E : SplitAbelianExtension A G H) (g : G) :
    ∃ (a : A) (h : H),
      g = E.inclusion (Multiplicative.ofAdd a) * E.splitting h := by
  have hkernel : g * (E.splitting (E.quotient g))⁻¹ ∈ E.quotient.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv,
      quotient_splitting_apply, mul_inv_cancel]
  rw [E.exact] at hkernel
  obtain ⟨a, ha⟩ := hkernel
  refine ⟨Multiplicative.toAdd a, E.quotient g, ?_⟩
  calc
    g = (g * (E.splitting (E.quotient g))⁻¹) *
        E.splitting (E.quotient g) := by
      simp only [inv_mul_cancel_right]
    _ = E.inclusion a * E.splitting (E.quotient g) := by rw [← ha]

/-- Kernel and quotient fixedness give full invariance. Paper: §4. -/
theorem invariant_of_kernel_and_quotient
    (E : SplitAbelianExtension A G H)
    {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : UnitaryRepresentation G V) (ξ : V)
    (hkernel : ∀ a : A,
      (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V) ξ = ξ)
    (hquotient : ∀ h : H,
      (π (E.splitting h) : V →L[ℂ] V) ξ = ξ) :
    π.IsInvariant ξ := by
  intro g
  obtain ⟨a, h, rfl⟩ := E.exists_kernel_mul_splitting g
  rw [map_mul]
  change
    (π (E.inclusion (Multiplicative.ofAdd a)) : V →L[ℂ] V)
        ((π (E.splitting h) : V →L[ℂ] V) ξ) = ξ
  rw [hquotient h, hkernel a]

end SplitAbelianExtension
end Connes
