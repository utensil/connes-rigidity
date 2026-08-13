/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Transport the concrete first-module semisimplicity proof into the paper-facing
predicate and expose the resulting Section 6 nonisomorphism theorem.
-/
import Connes.Paper.Section6.ModuleSemisimple
import Connes.Paper.Section6.NonisomorphismTransport

namespace Connes
namespace PaperModuleSemisimpleTransport

open Construction
open Construction.PaperKernel
open PaperNonisomorphism
open PaperModuleSemisimple

noncomputable section

abbrev Q := PaperKernel.Q
abbrev D := PaperKernel.D

/- The concrete first action is the product representation proved semisimple above. Paper: §6. -/
def paperFirstProductRepresentation : Representation k Q D :=
  PaperModuleSemisimple.firstProductRepresentation

/- The paper-facing first action agrees with the decomposed representation. Paper: §6. -/
theorem paper_qRepresentationOne_eq_firstProduct :
    qRepresentationOne =
      paperFirstProductRepresentation := by
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro d
  rcases d with ⟨u, c⟩
  apply Prod.ext
  · rfl
  · have hm := PaperKernel.sl3CActionHom.map_one
    change PaperKernel.sl3CActionEquiv (1 : SpecialLinear.SL3) =
      LinearEquiv.refl k PaperKernel.C at hm
    exact congrArg (fun e : PaperKernel.C ≃ₗ[k] PaperKernel.C => e c) hm

/- The actual first quotient module is semisimple, closing its §6 input. Paper: §6. -/
theorem paper_moduleOne_semisimple :
    moduleOneSemisimple := by
  change IsSemisimpleModule Ring
    (qRepresentationOne).asModule
  rw [paper_qRepresentationOne_eq_firstProduct]
  exact PaperModuleSemisimple.firstProduct_semisimple

/-- The two concrete paper groups are nonisomorphic. This is the public §6 endpoint. -/
theorem paperGroups_not_isomorphic :
    ¬ GroupsIsomorphic
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData)
      (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) :=
  PaperNonisomorphism.paperNotIsomorphic paper_moduleOne_semisimple

end
end PaperModuleSemisimpleTransport
end Connes
