/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Concrete completion records for the paper-facing algebraic arguments.
Paper: §§5--6.
-/
import Connes.PaperICCOrbits
import Connes.PaperModuleSemisimpleTransport
import Connes.PaperNonisomorphismTransport
import Connes.PaperNonisomorphismEmbedding

namespace Connes
namespace PaperConcreteCompletion

open Construction
open Construction.PaperKernel

noncomputable section

/-- The concrete orbit certificates for both Zhou actions. Paper: §5. -/
def paperICCDataPair : PaperICC.DataPair PaperKernel.paperActionData :=
  PaperICC.paper_dataPair

/-- ICC for the first concrete Zhou group. Paper: §5. -/
theorem paperGammaOne_icc :
    IsICC (PaperKernel.paperGammaOneOf PaperKernel.paperActionData) :=
  PaperICC.paper_gammaOne_icc

/-- ICC for the second concrete Zhou group. Paper: §5. -/
theorem paperGammaTwo_icc :
    IsICC (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) :=
  PaperICC.paper_gammaTwo_icc

/-- The concrete module inputs for Zhou's characteristic-kernel obstruction. Paper: §6. -/
def paperNonisomorphismData : PaperNonisomorphism.Data PaperKernel.paperActionData where
  moduleOne_semisimple := PaperModuleSemisimpleTransport.paper_moduleOne_semisimple
  moduleTwo_not_semisimple_under_quotient := fun σ =>
    PaperNonisomorphism.paper_moduleTwoAlong_not_semisimple σ
  characteristic_module_equiv := fun f =>
    PaperNonisomorphism.paperCharacteristicModuleEquiv f

/-- Nonisomorphism of the concrete Zhou groups. Paper: §6. -/
theorem paperGamma_not_isomorphic :
    ¬ GroupsIsomorphic
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData)
      (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) :=
  PaperNonisomorphism.not_isomorphic PaperKernel.paperActionData
    paperNonisomorphismData

end
end PaperConcreteCompletion
end Connes
