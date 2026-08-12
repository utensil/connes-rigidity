/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Algebraic identification of Zhou's actual dual coordinates. Paper: §3.
-/
import Mathlib
import Connes.Construction.PaperActionInstances
import Connes.PaperFactorIsomorphism

namespace Connes
namespace PaperDualCoordinates

open Construction
open Construction.PaperKernel

noncomputable section

abbrev k := Construction.k
abbrev A := Construction.A
abbrev V := PaperKernel.PaperV
abbrev VStar := PaperKernel.VStar
abbrev AVStar := PaperKernel.AVStar
abbrev C := PaperKernel.C
abbrev D := PaperKernel.D
abbrev DualCoordinates := PaperFactorIsomorphism.DualCoordinates

noncomputable def vStarDualEquiv : Module.Dual k VStar ≃ₗ[k] V :=
  (Module.evalEquiv k V).symm

def transposeToDual : (A →ₗ[k] V) →ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) where
  toFun f :=
    { toFun := fun φ =>
        { toFun := fun a => φ (f a)
          map_add' := by intro a b; simp
          map_smul' := by intro r a; simp }
      map_add' := by intro φ ψ; ext a; simp
      map_smul' := by intro r φ; ext a; simp }
  map_add' := by intro f g; ext φ a; simp
  map_smul' := by intro r f; ext φ a; simp

def transposeFromDual : (VStar →ₗ[k] Module.Dual k A) →ₗ[k]
    (A →ₗ[k] V) where
  toFun g :=
    { toFun := fun a =>
        (Module.evalEquiv k V).symm
          { toFun := fun φ => g φ a
            map_add' := by intro φ ψ; simp
            map_smul' := by intro r φ; simp }
      map_add' := by
        intro a b
        apply (Module.evalEquiv k V).injective
        ext φ
        simp
      map_smul' := by
        intro r a
        apply (Module.evalEquiv k V).injective
        ext φ
        simp }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro a
    apply (Module.evalEquiv k V).injective
    ext φ
    simp
  map_smul' := by
    intro r g
    apply LinearMap.ext
    intro a
    apply (Module.evalEquiv k V).injective
    ext φ
    simp

theorem transposeFromDual_left_inverse (f : A →ₗ[k] V) :
    transposeFromDual (transposeToDual f) = f := by
  apply LinearMap.ext
  intro a
  apply (Module.evalEquiv k V).injective
  ext φ
  simp [transposeFromDual, transposeToDual]

theorem transposeFromDual_right_inverse
    (g : VStar →ₗ[k] Module.Dual k A) :
    transposeToDual (transposeFromDual g) = g := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro a
  simp [transposeFromDual, transposeToDual]

noncomputable def transposeEquiv : (A →ₗ[k] V) ≃ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) :=
  LinearEquiv.ofLinear transposeToDual transposeFromDual
    (by apply LinearMap.ext; intro g; exact transposeFromDual_right_inverse g)
    (by apply LinearMap.ext; intro f; exact transposeFromDual_left_inverse f)

def dualTensorToPartial : Module.Dual k AVStar →ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) where
  toFun f :=
    { toFun := fun φ =>
        { toFun := fun a => f (a ⊗ₜ[k] φ)
          map_add' := by
            intro a b
            change f ((a + b) ⊗ₜ[k] φ) = f (a ⊗ₜ[k] φ) + f (b ⊗ₜ[k] φ)
            rw [TensorProduct.add_tmul, map_add]
          map_smul' := by
            intro r a
            change f ((r • a) ⊗ₜ[k] φ) = r • f (a ⊗ₜ[k] φ)
            simpa only [← TensorProduct.smul_tmul'] using f.map_smul r (a ⊗ₜ[k] φ) }
      map_add' := by
        intro φ ψ
        apply LinearMap.ext
        intro a
        change f (a ⊗ₜ[k] (φ + ψ)) =
          f (a ⊗ₜ[k] φ) + f (a ⊗ₜ[k] ψ)
        rw [TensorProduct.tmul_add, map_add]
      map_smul' := by
        intro r φ
        apply LinearMap.ext
        intro a
        change f (a ⊗ₜ[k] (r • φ)) = r • f (a ⊗ₜ[k] φ)
        simpa only [TensorProduct.tmul_smul] using f.map_smul r (a ⊗ₜ[k] φ) }
  map_add' := by intro f g; ext φ a; simp
  map_smul' := by intro r f; ext φ a; simp

def partialToDual : (VStar →ₗ[k] Module.Dual k A) →ₗ[k]
    Module.Dual k AVStar where
  toFun g := TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun φ => g φ a
          map_add' := by intro φ ψ; simp
          map_smul' := by intro r φ; simp }
      map_add' := by intro a b; ext φ; simp
      map_smul' := by intro r a; ext φ; simp }
  map_add' := by intro f g; apply TensorProduct.ext'; intro a φ; simp
  map_smul' := by intro r g; apply TensorProduct.ext'; intro a φ; simp

theorem partialToDual_left_inverse (f : Module.Dual k AVStar) :
    partialToDual (dualTensorToPartial f) = f := by
  apply LinearMap.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a φ
    rfl
  · intro x y hx hy
    simp only [map_add, hx, hy]

theorem partialToDual_right_inverse
    (g : VStar →ₗ[k] Module.Dual k A) :
    dualTensorToPartial (partialToDual g) = g := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro a
  rfl

noncomputable def dualTensorPartialEquiv : Module.Dual k AVStar ≃ₗ[k]
    (VStar →ₗ[k] Module.Dual k A) :=
  LinearEquiv.ofLinear dualTensorToPartial partialToDual
    (by apply LinearMap.ext; intro g; exact partialToDual_right_inverse g)
    (by apply LinearMap.ext; intro f; exact partialToDual_left_inverse f)

noncomputable def avDualEquiv : Module.Dual k AVStar ≃ₗ[k] A →ₗ[k] V :=
  dualTensorPartialEquiv.trans transposeEquiv.symm

/- The full algebraic dual splits over the two kernel summands. Paper: §3. -/
noncomputable def dualEquiv : Module.Dual k D ≃ₗ[k] DualCoordinates :=
  (Module.dualProdDualEquivDual k AVStar C).symm.trans
    (avDualEquiv.prodCongr (LinearEquiv.refl k (C →ₗ[k] k)))

end
end PaperDualCoordinates
end Connes
