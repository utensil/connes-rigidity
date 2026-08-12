/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete assembly of the Zhou §4 finite-index transfer data.
Paper: §4.
-/
import Connes.PaperFiniteExtensions

namespace Connes
namespace PaperPropertyTCompletion

open Construction
open Construction.PaperKernel
open PaperPropertyT

noncomputable section

/-- Assemble the actual finite-index transfer fields from relative inputs. Paper: §4. -/
def data
    (relativeOne : PropertyTTransfer.RelativeExtensionData
      (lambdaOneOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaOneKernelSubgroup PaperKernel.paperActionData))
    (relativeTwo : PropertyTTransfer.RelativeExtensionData
      (lambdaTwoOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaTwoKernelSubgroup PaperKernel.paperActionData)) :
    PaperPropertyT.Data PaperKernel.paperActionData where
  lambdaOne := relativeOne
  lambdaTwo := relativeTwo
  gammaOne := PaperFiniteExtensions.finiteExtensionOne
  gammaTwo := PaperFiniteExtensions.finiteExtensionTwo

/-- Property-(T) follows from EJZK and the two paper-relative spectral inputs. Paper: §4. -/
theorem completion
    (input : PaperPropertyT.EJZKInput)
    (relativeOne : PropertyTTransfer.RelativeExtensionData
      (lambdaOneOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaOneKernelSubgroup PaperKernel.paperActionData))
    (relativeTwo : PropertyTTransfer.RelativeExtensionData
      (lambdaTwoOf PaperKernel.paperActionData) SpecialLinear.sl3Group
      (lambdaTwoKernelSubgroup PaperKernel.paperActionData)) :
    HasKazhdanPropertyT
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData) ∧
      HasKazhdanPropertyT
        (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) := by
  exact PaperPropertyT.completion PaperKernel.paperActionData input
    (data relativeOne relativeTwo)

end
end PaperPropertyTCompletion
end Connes
