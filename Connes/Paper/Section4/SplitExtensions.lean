/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete split-extension presentations for Zhou §4. These expose the actual
semidirect-product inclusion, quotient, section, and conjugation used by the
spectral criterion; they do not prove the paper-specific spectral input.
-/
import Connes.Paper.Section4.PropertyT
import Connes.Foundation.GroupTheory.SplitAbelianExtension

namespace Connes
namespace PaperSplitExtensions

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

/- The first SL₃ extension as a split abelian extension. Paper: §4. -/
noncomputable def lambdaOne :
    (actions : PaperKernel.ActionData) →
    SplitAbelianExtension PaperKernel.D
      (lambdaOneOf actions) SpecialLinear.sl3Group
  | actions => {
  inclusion := SemidirectProduct.inl
  quotient := SemidirectProduct.rightHom
  splitting := SemidirectProduct.inr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative PaperKernel.D).toMonoidHom.comp
    (actions.thetaOne.comp sl3ToActingGroup)
  conjugation h a := by
    change
      (⟨1, (h : SpecialLinear.SL3)⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaOne.comp sl3ToActingGroup)) *
        (⟨Multiplicative.ofAdd a, 1⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaOne.comp sl3ToActingGroup)) *
        (⟨1, (h : SpecialLinear.SL3)⟩ :
            SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaOne.comp sl3ToActingGroup))⁻¹ =
      (⟨(actions.thetaOne.comp sl3ToActingGroup) h
          (Multiplicative.ofAdd a), 1⟩ :
        SemidirectProduct (Multiplicative PaperKernel.D)
          SpecialLinear.SL3
          (actions.thetaOne.comp sl3ToActingGroup))
    ext <;> simp }

/- The second SL₃ extension as a split abelian extension. Paper: §4. -/
noncomputable def lambdaTwo :
    (actions : PaperKernel.ActionData) →
    SplitAbelianExtension PaperKernel.D
      (lambdaTwoOf actions) SpecialLinear.sl3Group
  | actions => {
  inclusion := SemidirectProduct.inl
  quotient := SemidirectProduct.rightHom
  splitting := SemidirectProduct.inr
  quotient_splitting := SemidirectProduct.rightHom_comp_inr
  exact := SemidirectProduct.range_inl_eq_ker_rightHom.symm
  action := (MulAutMultiplicative PaperKernel.D).toMonoidHom.comp
    (actions.thetaTwo.comp sl3ToActingGroup)
  conjugation h a := by
    change
      (⟨1, (h : SpecialLinear.SL3)⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaTwo.comp sl3ToActingGroup)) *
        (⟨Multiplicative.ofAdd a, 1⟩ :
          SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaTwo.comp sl3ToActingGroup)) *
        (⟨1, (h : SpecialLinear.SL3)⟩ :
            SemidirectProduct (Multiplicative PaperKernel.D)
            SpecialLinear.SL3
            (actions.thetaTwo.comp sl3ToActingGroup))⁻¹ =
      (⟨(actions.thetaTwo.comp sl3ToActingGroup) h
          (Multiplicative.ofAdd a), 1⟩ :
        SemidirectProduct (Multiplicative PaperKernel.D)
          SpecialLinear.SL3
          (actions.thetaTwo.comp sl3ToActingGroup))
    ext <;> simp }

end

end PaperSplitExtensions
end Connes
