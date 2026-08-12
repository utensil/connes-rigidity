/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped non-isomorphism scaffold for Zhou §6. The characteristic normal
subgroup and semisimplicity obstruction are named at the paper's boundaries;
their proofs are intentionally deferred.
-/
import Mathlib
import Connes.Core
import Connes.Construction
import Connes.Foundation.GroupTheory.Sp4
import Connes.Foundation.LinearAlgebra.Semisimple
import Connes.Foundation.LinearAlgebra.QuadraticCocycle

namespace Connes
namespace Nonisomorphism

open Construction

namespace Cocycle

/-- Finite symplectic scalar field. Paper: §6. -/
abbrev F := ZMod 2
/-- Finite symplectic acting group. Paper: §6. -/
abbrev Q := OpenAIPort.ModTwoSymplecticGroup
/-- Matrix-indexed symplectic module. Paper: §6. -/
abbrev I := OpenAIPort.SymplecticIndex
/-- Coordinate carrier for the finite module. Paper: §6. -/
abbrev W := OpenAIPort.ModTwoSpace

/-- Natural matrix action on the finite module. Paper: §6. -/
def action (q : Q) (v : W) : W :=
  q • v

/-- Quadratic refinement used for the finite cocycle. Paper: §6. -/
def refinement (v : W) : F :=
  OpenAIPort.standardQuadraticForm v

/-- Finite cocycle obtained from the quadratic refinement. Paper: §6. -/
def cocycle (q : Q) (v : W) : F :=
  refinement (action q⁻¹ v) + refinement v

/-- The quadratic defect is linear in the module variable. Paper: §2. -/
theorem cocycle_is_linear (q : Q) :
    ∃ ell : W →ₗ[F] F, ∀ v, ell v = cocycle q v := by
  refine ⟨OpenAIPort.quadraticDefectLinear q, ?_⟩
  intro v
  rfl

/-- The finite defects satisfy the cocycle identity. Paper: §2. -/
theorem cocycle_identity (p q : Q) (v : W) :
    cocycle (p * q) v = cocycle q (action p⁻¹ v) + cocycle p v := by
  native_decide +revert

/-- Coordinate form of a linear functional. Paper: §6. -/
def coordinateFunctional (c v : W) : F :=
  ∑ i, c i * v i

/-- Linear coboundary predicate for the finite cocycle. Paper: §6. -/
def IsLinearCoboundary : Prop :=
  ∃ f : W →ₗ[F] F, ∀ q v,
    cocycle q v = f (action q⁻¹ v) + f v

/-- Exhaustive finite check for coordinate coboundaries. Paper: §6. -/
private theorem no_coordinate_coboundary :
    ¬ ∃ c : W, ∀ q v,
      cocycle q v = coordinateFunctional c (action q⁻¹ v) + coordinateFunctional c v := by
  native_decide

end Cocycle

/-- Reduced first-module carrier used by the local finite obstruction. Paper: §6. -/
def ReducedDOneModule := D
/-- Reduced second-module carrier used by the local finite obstruction. Paper: §6. -/
def ReducedDTwoModule := D

/-- Reduced first semisimplicity boundary. Paper: §6. -/
def ReducedDOneSemisimple : Prop := True
/-- Reduced extension-splitting boundary for the second module. Paper: §6.

This is the finite quadratic extension obstruction currently represented by the
available carrier; it is not yet the full semisimplicity predicate for D₂. -/
def ReducedDTwoSemisimple : Prop := Cocycle.IsLinearCoboundary

/-- Reduced first-module witness. Paper: §6. -/
theorem reduced_DOne_semisimple : ReducedDOneSemisimple := by
  trivial

/-- The finite quadratic cocycle is not a linear coboundary. Paper: §6. -/
theorem cocycle_not_coboundary : ¬ Cocycle.IsLinearCoboundary := by
  intro h
  obtain ⟨f, hf⟩ := h
  let c : Cocycle.W := fun i => f (Pi.single i 1)
  apply Cocycle.no_coordinate_coboundary
  refine ⟨c, ?_⟩
  intro q v
  have hrep : ∀ w : Cocycle.W, f w = Cocycle.coordinateFunctional c w := by
    intro w
    calc
      f w = f (∑ i, w i • (Pi.single i (1 : Cocycle.F))) := by
        congr 1
        ext j
        simp [Pi.single_apply]
      _ = ∑ i, f (w i • (Pi.single i (1 : Cocycle.F))) := by
        rw [map_sum]
      _ = ∑ i, w i * f (Pi.single i (1 : Cocycle.F)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_eq_mul]
      _ = Cocycle.coordinateFunctional c w := by
        simp only [c, Cocycle.coordinateFunctional]
        apply Finset.sum_congr rfl
        intro i hi
        rw [mul_comm]
  rw [hf q v, hrep, hrep]

/-- Reduced second-module obstruction. Paper: §6. -/
theorem reduced_DTwo_not_semisimple : ¬ ReducedDTwoSemisimple := by
  simpa only [ReducedDTwoSemisimple] using cocycle_not_coboundary

/-- Available quotient normal-subgroup obstruction. Paper: §6.

This records the proved finite quotient consequences; identifying the full
characteristic Dᵢ inside the real semidirect products remains open. -/
def normal_module_characteristic : Prop :=
  Sp4.no_nontrivial_normal_elementary_abelian_subgroup ∧
    SpecialLinear.no_nontrivial_abelian_normal_subgroup

/-- Proof of the available quotient normal-subgroup obstruction. Paper: §6. -/
theorem normal_module_characteristic_proof : normal_module_characteristic := by
  exact ⟨Sp4.no_nontrivial_normal_elementary_abelian_subgroup_proof,
    SpecialLinear.no_nontrivial_abelian_normal_subgroup_proof⟩

/-- Inputs for the characteristic-module obstruction. Paper: §6. -/
structure PaperNonisomorphismData (actions : ActionData) where
  moduleOneSemisimple : Prop
  moduleTwoSemisimple : Prop
  moduleOne_semisimple : moduleOneSemisimple
  moduleTwo_not_semisimple : ¬ moduleTwoSemisimple
  semisimplicity_preserved :
    ∀ f : gammaOneOf actions ≃* gammaTwoOf actions,
      moduleOneSemisimple → moduleTwoSemisimple

/-- The headline nonisomorphism target is false for the current placeholder
groups. Paper: §6. -/
theorem gammaOne_nonisomorphism_target_false :
    ¬ (¬ GroupsIsomorphic gammaOne gammaTwo) := by
  intro h
  exact h gammaOne_groupsIsomorphic_gammaTwo

/-- Group nonisomorphism conclusion from the characteristic-module obstruction.
Paper: §6. -/
theorem gammaOne_not_isomorphic_gammaTwo
    (actions : ActionData) (data : PaperNonisomorphismData actions) :
    ¬ GroupsIsomorphic (gammaOneOf actions) (gammaTwoOf actions) := by
  rintro ⟨f⟩
  apply data.moduleTwo_not_semisimple
  exact data.semisimplicity_preserved f data.moduleOne_semisimple

end Nonisomorphism
end Connes
