/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the characteristic-two symplectic construction
in Zhou §2. The OpenAI/ten-proofs Connes formalization is a public reading
reference, pinned at commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, and is
not a dependency of this file. Modifications: the paper's local symplectic
API is introduced independently and its difficult facts remain open.
-/
import Mathlib

namespace Connes
namespace Symplectic

/-- Characteristic-two scalar field. Paper: §2. -/
abbrev F := ZMod 2
/-- Four-dimensional symplectic module. Paper: §2. -/
abbrev V := Fin 4 → F

/-- Symplectic form boundary. Paper: §2. -/
def form (v w : V) : F :=
  v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2

/-- Quadratic refinement boundary. Paper: §2. -/
def quadraticRefinement (v : V) : F :=
  v 0 * v 1 + v 2 * v 3

/-- Polarization operation. Paper: §2. -/
def polarization (q : V → F) (v w : V) : F :=
  q (v + w) - q v - q w

/-- Polarization compatibility. Paper: §2. -/
theorem refinement_polarizes_to_form :
    ∀ v w : V, polarization quadraticRefinement v w = form v w := by
  intro v w
  simp [polarization, quadraticRefinement, form]
  ring

/-- Symplectic group carrier. Paper: §2. -/
abbrev Sp4 := Matrix.symplecticGroup (Fin 2) F

/-- Cocycle boundary for the refinement. Paper: §2. -/
def cocycle (g : V ≃ₗ[F] V) : V → F :=
  fun v => quadraticRefinement (g v) - quadraticRefinement v

/- A linear automorphism preserving the symplectic form. Paper: §2. -/
structure SymplecticLinearEquiv where
  toLinearEquiv : V ≃ₗ[F] V
  map_form' : ∀ v w, form (toLinearEquiv v) (toLinearEquiv w) = form v w

/-- Linear cocycle witness. Paper: §2. -/
theorem cocycle_is_linear (g : SymplecticLinearEquiv)
    : ∃ ℓ : V →ₗ[F] F, ∀ v, ℓ v = cocycle g.toLinearEquiv v := by
  let d : V → F := cocycle g.toLinearEquiv
  have hadd : ∀ v w, d (v + w) = d v + d w := by
    intro v w
    have hgw := refinement_polarizes_to_form (g.toLinearEquiv v) (g.toLinearEquiv w)
    have hvw := refinement_polarizes_to_form v w
    dsimp [d, cocycle]
    rw [show g.toLinearEquiv (v + w) = g.toLinearEquiv v + g.toLinearEquiv w by
      simp]
    have hpolar :
        polarization quadraticRefinement (g.toLinearEquiv v) (g.toLinearEquiv w) =
          polarization quadraticRefinement v w := by
      calc
        _ = form (g.toLinearEquiv v) (g.toLinearEquiv w) := hgw
        _ = form v w := g.map_form' v w
        _ = _ := hvw.symm
    dsimp [polarization] at hpolar
    linear_combination hpolar
  let ℓ : V →ₗ[F] F :=
    { toFun := d
      map_add' := hadd
      map_smul' := by
        intro a v
        have ha : a = 0 ∨ a = 1 := by
          fin_cases a
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases ha with rfl | rfl <;>
          simp [d, cocycle, quadraticRefinement, smul_eq_mul] }
  exact ⟨ℓ, fun v => rfl⟩

/-- Cocycle composition law. Paper: §2. -/
theorem cocycle_identity (g h : V ≃ₗ[F] V) :
    cocycle (g.trans h) = fun v => cocycle h (g v) + cocycle g v := by
  funext v
  simp only [cocycle, LinearEquiv.trans_apply]
  ring

/-- Symplectic transitivity boundary. Paper: §2. -/
theorem sp4_transitive_on_nonzero :
    ∀ v : V, v ≠ 0 → ∃ g : V ≃ₗ[F] V, g v = fun _ => 1 := by
  intro v hv
  let w : V := fun _ => 1
  have hw : w ≠ 0 := by
    intro h
    have h0 := congr_fun h 0
    simp [w] at h0
  by_cases hvw : v = w
  · subst v
    exact ⟨LinearEquiv.refl F V, by rfl⟩
  have hli : LinearIndependent F ![v, w] :=
    (LinearIndependent.pair_iff' hv).2 (by
      intro a
      have ha : a = 0 ∨ a = 1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases ha with rfl | rfl
      · simpa only [zero_smul] using Ne.symm hw
      · simpa only [one_smul] using hvw)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one hli.linearIndepOn_id
  have fv : f v = 1 := hf v ⟨0, by rfl⟩
  have fw : f w = 1 := hf w ⟨1, by rfl⟩
  let x : V := v + w
  have hx : f x = 2 := by
    dsimp [x]
    rw [map_add, fv, fw]
    norm_num
  let e : V ≃ₗ[F] V := Module.reflection hx
  refine ⟨e, ?_⟩
  dsimp [e, x]
  rw [Module.reflection_apply, fv]
  rw [ZModModule.sub_eq_add]
  simp only [one_smul]
  rw [← add_assoc, ZModModule.add_self, zero_add]

end Symplectic
end Connes
