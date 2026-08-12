/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

The first-coordinate formula for Zhou's contragredient action. Paper: §3.
-/
import Connes.Foundation.OperatorAlgebra.PaperDualActionConjugacyAlgebra

set_option maxHeartbeats 5000000

namespace Connes
namespace PaperDualActionConjugacyFirst

open Construction
open Construction.PaperKernel
open PaperDualActions
open PaperDualCoordinates
open PaperFactorIsomorphism
open PaperDualActionConjugacyAlgebra

noncomputable section

abbrev k := Construction.k
abbrev H := Construction.H
abbrev A := Construction.A
abbrev PaperV := PaperKernel.PaperV

/- Precomposition by the first inverse action produces `zAction`. Paper: §3. -/
theorem first_coordinate_eq_zAction (h : H)
    (z : A →ₗ[k] PaperV) (lam : PaperKernel.C →ₗ[k] k) :
    avDualEquiv
        ((LinearMap.coprod (avDualEquiv.symm z) lam) ∘ₗ
          (paperThetaOneLinear h).symm ∘ₗ
            LinearMap.inl k PaperKernel.AVStar PaperKernel.C) =
      zAction h z := by
  apply LinearMap.ext
  intro a
  apply (Module.evalEquiv k PaperV).injective
  ext φ
  simp only [Module.evalEquiv_apply, Module.Dual.eval_apply]
  rw [avDualEquiv_eval]
  simp only [LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.coprod_apply]
  change (avDualEquiv.symm z)
      ((paperThetaOneLinear h).symm (a ⊗ₜ[k] φ, 0)).1 +
      lam ((paperThetaOneLinear h).symm (a ⊗ₜ[k] φ, 0)).2 =
    φ (zAction h z a)
  rw [paperThetaOne_symm_inl]
  simp only [LinearMap.coprod_apply, map_zero, add_zero]
  rw [zAction_apply]
  simp [avStarAction, tensorProductLinearEquiv, qVAction,
    qVStarActionHom]
  rw [avDualEquiv_symm_eval]
  rfl

end
end PaperDualActionConjugacyFirst
end Connes
