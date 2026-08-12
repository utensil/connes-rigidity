/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped ICC scaffold for Zhou §5. It follows the dependency boundary
from the public OpenAI/ten-proofs reference but contains no imported reference
implementation. The SL₃ conjugacy orbit and generic semidirect transfer are
proved here; the paper-specific module orbit and gamma conclusions remain
open.
-/
import Mathlib
import Connes.Core
import Connes.Construction
import Connes.Foundation.GroupTheory.SpecialLinear
import Connes.Foundation.GroupTheory.SemidirectICC

namespace Connes
namespace ICC

universe u

open Construction

/-- Infinite orbit represented by an explicit orbit map. Paper: §5. -/
def InfiniteOrbit (G X : Type*) (orbit : G → X) : Prop :=
  (Set.range orbit).Infinite

/-- The proved SL₃ conjugacy orbits are infinite. Paper: §5. -/
theorem sl3_infinite_orbits :
    ∀ g : SpecialLinear.SL3, g ≠ 1 →
      InfiniteOrbit SpecialLinear.SL3 SpecialLinear.SL3
        (fun h => h * g * h⁻¹) := by
  intro g hg
  have hicc := SpecialLinear.sl3_isICC.2 g hg
  have heq :
      Set.range (fun h : SpecialLinear.SL3 => h * g * h⁻¹) =
        conjugacyClass SpecialLinear.sl3Group g := by
    ext y
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
  change (Set.range fun h : SpecialLinear.SL3 => h * g * h⁻¹).Infinite
  rw [heq]
  exact hicc

/-- Module-orbit witness for the paper kernel. Paper: §5. -/
structure ModuleOrbitWitness where
  action : SpecialLinear.SL3 →* MulAut (Multiplicative D)
  infinite_orbit : ∀ d : D, d ≠ 0 →
    (Set.range fun h : SpecialLinear.SL3 =>
      (action h (Multiplicative.ofAdd d)).toAdd).Infinite

/-- Infinite module-orbit predicate. Paper: §5. -/
def module_infinite_orbits (witness : ModuleOrbitWitness) : Prop :=
  ∀ d : D, d ≠ 0 →
    (Set.range fun h : SpecialLinear.SL3 =>
      (witness.action h (Multiplicative.ofAdd d)).toAdd).Infinite

/-- Module-orbit witness projection. Paper: §5. -/
theorem module_infinite_orbits_of_witness (witness : ModuleOrbitWitness) :
    module_infinite_orbits witness :=
  witness.infinite_orbit

/-- ICC transfer for a split quotient. Paper: §5. -/
theorem isICC_of_split_quotient
    (G H : CountableDiscreteGroup.{u})
    (projection : G →* H) (section_ : H →* G)
    (hsection : ∀ h : H, projection (section_ h) = h)
    (hH : IsICC H)
    (hkernel : ∀ x : G, projection x = 1 → x ≠ 1 →
      (OpenAIPort.splitConjugationOrbit G H section_ x).Infinite) :
    IsICC G :=
  OpenAIPort.isICC_of_split_quotient G H projection section_ hsection hH hkernel

/-- ICC transfer for a semidirect product with infinite module orbits. Paper: §5. -/
theorem semidirect_isICC
    (A H : CountableDiscreteGroup.{u}) (action : H →* MulAut A)
    (hH : IsICC H)
    (horbit : ∀ a : A, a ≠ 1 →
      (Set.range fun h : H => action h a).Infinite) :
    IsICC (OpenAIPort.semidirectCountableGroup A H action) :=
  OpenAIPort.semidirect_isICC A H action hH horbit

/-- Inputs for the two paper semidirect-product ICC arguments. Paper: §5. -/
structure ICCData (actions : ActionData) where
  actingGroup_icc : IsICC actingGroup
  gammaOne_orbits : ∀ a : GammaKernel, a ≠ 1 →
    (Set.range fun h : H => actions.thetaOneAction h a).Infinite
  gammaTwo_orbits : ∀ a : GammaKernel, a ≠ 1 →
    (Set.range fun h : H => actions.thetaTwoAction h a).Infinite

private theorem kernel_nontrivial :
    Multiplicative.ofAdd (1 : D) ≠ (1 : GammaKernel) := by
  intro h
  have h0 : (1 : D) = 0 := congrArg Multiplicative.toAdd h
  have h1 := congrArg (fun d : D => (d.1.1 0).coeff 0) h0
  norm_num at h1

private theorem gammaOne_kernel_central (n : GammaKernel) (x : GammaOneCarrier) :
    (SemidirectProduct.inl n : GammaOneCarrier) * x =
      x * SemidirectProduct.inl n := by
  apply SemidirectProduct.ext
  · change n * x.left = x.left * n
    exact mul_comm _ _
  · change (1 : H) * x.right = x.right * 1
    simp

private theorem gammaTwo_kernel_central (n : GammaKernel) (x : GammaTwoCarrier) :
    (SemidirectProduct.inl n : GammaTwoCarrier) * x =
      x * SemidirectProduct.inl n := by
  apply SemidirectProduct.ext
  · change n * x.left = x.left * n
    exact mul_comm _ _
  · change (1 : H) * x.right = x.right * 1
    simp

/-- The identity-action placeholder has a nontrivial central kernel element,
so its ICC target is false. Paper: §5. -/
theorem gammaOne_not_icc : ¬ IsICC gammaOne := by
  intro hICC
  let n : GammaKernel := Multiplicative.ofAdd (1 : D)
  let g : gammaOne := SemidirectProduct.inl n
  have hg : g ≠ 1 := by
    intro h
    change (SemidirectProduct.inl n : GammaOneCarrier) = (1 : GammaOneCarrier) at h
    have h0 := congrArg (fun y : GammaOneCarrier => y.left) h
    change n = 1 at h0
    exact kernel_nontrivial h0
  have hcentral : ∀ x : gammaOne, g * x = x * g := by
    intro x
    let x' : GammaOneCarrier := x
    have hx := gammaOne_kernel_central n x'
    exact hx
  have hsubset : conjugacyClass gammaOne g ⊆ {g} := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change x * g * x⁻¹ = g
    rw [← hcentral x]
    simp [mul_assoc]
  have hfinite : (conjugacyClass gammaOne g).Finite :=
    (Set.finite_singleton g).subset hsubset
  exact hfinite.not_infinite (hICC.2 g hg)

/-- The identity-action placeholder has a nontrivial central kernel element,
so its ICC target is false. Paper: §5. -/
theorem gammaTwo_not_icc : ¬ IsICC gammaTwo := by
  intro hICC
  let n : GammaKernel := Multiplicative.ofAdd (1 : D)
  let g : gammaTwo := SemidirectProduct.inl n
  have hg : g ≠ 1 := by
    intro h
    change (SemidirectProduct.inl n : GammaTwoCarrier) = (1 : GammaTwoCarrier) at h
    have h0 := congrArg (fun y : GammaTwoCarrier => y.left) h
    change n = 1 at h0
    exact kernel_nontrivial h0
  have hcentral : ∀ x : gammaTwo, g * x = x * g := by
    intro x
    let x' : GammaTwoCarrier := x
    have hx := gammaTwo_kernel_central n x'
    exact hx
  have hsubset : conjugacyClass gammaTwo g ⊆ {g} := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    change x * g * x⁻¹ = g
    rw [← hcentral x]
    simp [mul_assoc]
  have hfinite : (conjugacyClass gammaTwo g).Finite :=
    (Set.finite_singleton g).subset hsubset
  exact hfinite.not_infinite (hICC.2 g hg)

/-- First ICC conclusion from the paper's orbit hypotheses. Paper: §5. -/
theorem gammaOne_icc (actions : ActionData) (data : ICCData actions) :
    IsICC (gammaOneOf actions) := by
  exact semidirect_isICC kernelGroup actingGroup actions.thetaOneAction
    data.actingGroup_icc data.gammaOne_orbits

/-- Second ICC conclusion from the paper's orbit hypotheses. Paper: §5. -/
theorem gammaTwo_icc (actions : ActionData) (data : ICCData actions) :
    IsICC (gammaTwoOf actions) := by
  exact semidirect_isICC kernelGroup actingGroup actions.thetaTwoAction
    data.actingGroup_icc data.gammaTwo_orbits

end ICC
end Connes
