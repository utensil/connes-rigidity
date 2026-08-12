/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete completion boundary for Zhou's Theorem A. Paper: §§3--7.
-/
import Connes.PaperSpectralPropertyT
import Connes.Foundation.OperatorAlgebra.PaperSpectralFiniteDetection
import Connes.Foundation.OperatorAlgebra.PaperConcreteFactor
import Connes.PaperConcreteCompletion

namespace Connes
namespace PaperTheoremACompletion

open Construction
open Construction.PaperKernel

noncomputable section

/- The concrete headline follows from the cited EJZK property-(T) input.
All remaining spectral, factor, ICC, and nonisomorphism certificates are
constructed internally. Paper: §§7. -/
theorem theoremA (propertyTInput : PaperPropertyT.EJZKInput) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ GroupsIsomorphic Γ₁ Γ₂ := by
  have hT := PaperSpectralPropertyT.completion_of_spectralData
    propertyTInput PaperSpectralFiniteDetection.lambdaOneSpectralData
      PaperSpectralFiniteDetection.lambdaTwoSpectralData
  have hFactor := PaperConcreteFactor.groupFactors_isomorphic
  have hNoniso := PaperConcreteCompletion.paperGamma_not_isomorphic
  exact ⟨PaperKernel.paperGammaOneOf PaperKernel.paperActionData,
    PaperKernel.paperGammaTwoOf PaperKernel.paperActionData,
    hT.1, hT.2, PaperConcreteCompletion.paperGammaOne_icc,
    PaperConcreteCompletion.paperGammaTwo_icc, hFactor, hNoniso⟩

end
end PaperTheoremACompletion
end Connes
