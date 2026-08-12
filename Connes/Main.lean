/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Completion boundary for Zhou's Theorem A. The headline now uses the actual
paper-shaped `PaperKernel` carriers. Its fields are the remaining proof
obligations for the explicit construction, rather than facts about the
legacy identity-action scaffold.
-/
import Connes.Core
import Connes.Construction
import Connes.PaperFactorIsomorphism
import Connes.PaperPropertyT
import Connes.PaperICC
import Connes.PaperNonisomorphism
import Connes.PaperTheoremACompletion

namespace Connes

open Construction

/-- The four Zhou §§3--6 inputs for the actual tensor-kernel groups. Paper: §7. -/
structure PaperTheoremAData
    (actions : Construction.PaperKernel.ActionData)
    [MeasurableSpace PaperFactorIsomorphism.DualCoordinates] where
  propertyTInput : PaperPropertyT.EJZKInput
  propertyT : PaperPropertyT.Data actions
  icc : PaperICC.DataPair actions
  factor : PaperFactorIsomorphism.PaperFactorData actions
  nonisomorphism : PaperNonisomorphism.Data actions

/-- Generic completion of the four headline properties from supplied data.
Paper: §7. -/
theorem theoremA_of_data
    (actions : Construction.PaperKernel.ActionData)
    [MeasurableSpace PaperFactorIsomorphism.DualCoordinates]
    (data : PaperTheoremAData actions) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ GroupsIsomorphic Γ₁ Γ₂ := by
  have hT := PaperPropertyT.completion actions data.propertyTInput data.propertyT
  have hICC₁ := PaperICC.gammaOne_icc actions data.icc
  have hICC₂ := PaperICC.gammaTwo_icc actions data.icc
  have hFactor := PaperFactorIsomorphism.groupFactors_isomorphic data.factor
  have hNoniso := PaperNonisomorphism.not_isomorphic actions data.nonisomorphism
  exact ⟨Construction.PaperKernel.paperGammaOneOf actions,
    Construction.PaperKernel.paperGammaTwoOf actions,
    hT.1, hT.2, hICC₁, hICC₂, hFactor, hNoniso⟩

/- Zhou's Theorem A. The only external mathematical input is the cited EJZK
property-(T) theorem for `EL₃(𝔽₂[t])`; every construction and all other
paper arguments are proved in this project. Paper: §7. -/
theorem theoremA
    (hEJZK : HasKazhdanPropertyT SpecialLinear.elementaryGroup) :
    ∃ Γ₁ Γ₂ : CountableDiscreteGroup.{0},
      HasKazhdanPropertyT Γ₁ ∧ HasKazhdanPropertyT Γ₂ ∧
      IsICC Γ₁ ∧ IsICC Γ₂ ∧
      TracialGroupFactorsIsomorphic Γ₁ Γ₂ ∧
      ¬ GroupsIsomorphic Γ₁ Γ₂ := by
  exact PaperTheoremACompletion.theoremA
    ⟨hEJZK⟩

end Connes
