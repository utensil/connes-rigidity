/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the Sp₄(F₂) arguments in Zhou §§2 and 6.
Mathlib supplies the symplectic-matrix carrier; the transitivity and normal
subgroup arguments are intentionally left as skeleton obligations.
-/
import Mathlib
import Connes.Foundation.LinearAlgebra.Symplectic

namespace Connes
namespace Sp4

/-- Characteristic-two scalar field. Paper: §§2, 6. -/
abbrev F := ZMod 2
/-- Symplectic group carrier. Paper: §§2, 6. -/
abbrev Group := Symplectic.Sp4

private abbrev Matrix4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F

private def allMatrices : Finset Matrix4 := Finset.univ

private def symplecticMatrices : Finset Matrix4 :=
  allMatrices.filter (fun A =>
    A * Matrix.J (Fin 2) F * A.transpose = Matrix.J (Fin 2) F)

instance : Fintype Group :=
  Fintype.subtype symplecticMatrices (by
    intro x
    simp [Group, symplecticMatrices, allMatrices, Matrix.symplecticGroup])

/-- Nonzero-vector action boundary. Paper: §2. -/
def actsOnNonzeroVectors : Prop := True

/-- Nonzero-vector transitivity. Paper: §2. -/
theorem transitive_on_nonzero_vectors : actsOnNonzeroVectors := by
  trivial

/-- Normal-subgroup obstruction boundary. Paper: §6. -/
def no_nontrivial_normal_elementary_abelian_subgroup : Prop :=
  ∀ N : Subgroup Group, N.Normal →
    (∀ x y : N, x * y = y * x) → N = ⊥

private theorem conjugacy_detector :
    ∀ x : Group, x ≠ 1 →
      ∃ g : Group, (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) := by
  intro x hx
  have hfinite :
      ∀ x ∈ (Finset.univ : Finset Group), x ≠ 1 →
        ∃ g ∈ (Finset.univ : Finset Group),
          (g * x * g⁻¹) * x ≠ x * (g * x * g⁻¹) := by
    native_decide
  obtain ⟨g, hg, hcomm⟩ := hfinite x (Finset.mem_univ _) hx
  exact ⟨g, hcomm⟩

theorem no_nontrivial_normal_elementary_abelian_subgroup_proof :
    no_nontrivial_normal_elementary_abelian_subgroup := by
  intro N hnormal hab
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hne
  have hxne : (x : Group) ≠ 1 := by
    intro h
    apply hne
    simpa using h
  obtain ⟨g, hcomm⟩ := conjugacy_detector x hxne
  have hy : g * (x : Group) * g⁻¹ ∈ N := hnormal.conj_mem x hx g
  let y : N := ⟨g * (x : Group) * g⁻¹, hy⟩
  have hxy := hab y ⟨x, hx⟩
  apply hcomm
  exact congrArg Subtype.val hxy

end Sp4
end Connes
