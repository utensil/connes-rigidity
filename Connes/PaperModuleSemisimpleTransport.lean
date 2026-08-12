/-
Copyright (c) 2026 utensil. All rights reserved.
Released under Apache 2.0. See LICENSE.

Transport the concrete first-module semisimplicity proof into the paper-facing
predicate and expose the resulting Section 6 nonisomorphism theorem.
-/
import Connes.PaperModuleSemisimple
import Connes.PaperNonisomorphismTransport

namespace Connes
namespace PaperModuleSemisimpleTransport

open Construction
open Construction.PaperKernel
open PaperNonisomorphism
open PaperModuleSemisimple

noncomputable section

abbrev Q := PaperKernel.Q
abbrev D := PaperKernel.D

/- The concrete first action is the product representation proved semisimple above. Paper: §4. -/
def paperFirstProductRepresentation : Representation k Q D :=
  PaperModuleSemisimple.firstProductRepresentation

/- The paper-facing first action agrees with the decomposed representation. Paper: §4. -/
theorem paper_qRepresentationOne_eq_firstProduct :
    qRepresentationOne PaperKernel.paperActionData =
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

/- The actual first quotient module is semisimple, closing its §4 input. Paper: §4. -/
theorem paper_moduleOne_semisimple :
    moduleOneSemisimple PaperKernel.paperActionData := by
  change IsSemisimpleModule Ring
    (qRepresentationOne PaperKernel.paperActionData).asModule
  rw [paper_qRepresentationOne_eq_firstProduct]
  exact PaperModuleSemisimple.firstProduct_semisimple

/- The concrete paper-shaped groups are nonisomorphic from the proved first module. Paper: §6. -/
theorem paperGroups_not_isomorphic :
    ¬ GroupsIsomorphic
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData)
      (PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) :=
  PaperNonisomorphism.paperNotIsomorphic paper_moduleOne_semisimple

end
end PaperModuleSemisimpleTransport
end Connes
