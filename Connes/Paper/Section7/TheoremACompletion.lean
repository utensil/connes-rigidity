/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0
-/
import Connes.Paper.Section4.SpectralPropertyT
import Connes.Paper.Section4.SpectralFiniteDetection
import Connes.Paper.Section3.FactorClosure
import Connes.Paper.Section5.ICCOrbits
import Connes.Paper.Section6.ModuleSemisimpleTransport

/-!
Concrete completion boundary for Zhou's Theorem A. Paper: §§3--7.
-/

namespace Connes
namespace PaperTheoremACompletion

open Construction
open Construction.PaperKernel

noncomputable section

/-- The concrete headline follows from the cited EJZK property-(T) input.
All remaining spectral, factor, ICC, and nonisomorphism certificates are
constructed internally. Paper: §§7. -/
theorem theoremA (propertyTInput : PaperPropertyT.EJZKInput) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ Nonempty (Γ₁ ≃* Γ₂) := by
  have hT := PaperSpectralPropertyT.completion_of_spectralData
    propertyTInput PaperSpectralFiniteDetection.lambdaOneSpectralData
      PaperSpectralFiniteDetection.lambdaTwoSpectralData
  have hFactor := PaperFactorClosure.paperGroupFactors_isomorphic
  have hNoniso := PaperModuleSemisimpleTransport.paperGroups_not_isomorphic
  exact ⟨PaperKernel.paperGammaOneOf PaperKernel.paperActionData,
    PaperKernel.paperGammaTwoOf PaperKernel.paperActionData,
    hT.1, hT.2, PaperICC.paper_gammaOne_icc,
    PaperICC.paper_gammaTwo_icc, hFactor, hNoniso⟩

end
end PaperTheoremACompletion
end Connes
