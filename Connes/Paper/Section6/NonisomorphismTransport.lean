/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

This file exposes the concrete Section 6 module-equivalence conclusion for
the actual Zhou carriers. The proof uses the public characteristic-kernel
and quotient transport files in this project.
-/

import Connes.Paper.Section6.QuotientModuleTransport
import Connes.Paper.Section6.NonisomorphismEmbedding

set_option maxHeartbeats 1600000

namespace Connes
namespace PaperNonisomorphism

open Construction
open Construction.PaperKernel
open PaperCharacteristicTransport

noncomputable section

/- A group isomorphism induces the module equivalence required in Section 6 (Zhou §6). -/
theorem paperCharacteristicModuleEquiv
    (f : PaperKernel.paperGammaOneOf PaperKernel.paperActionData ≃*
      PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) :
    ∃ σ : PaperKernel.Q ≃* PaperKernel.Q, Nonempty
      ((qRepresentationOne).asModule ≃ₗ[Ring]
        (qRepresentationTwoAlong σ).asModule) := by
  have hchar : Subgroup.map f.toMonoidHom
      (kernelSubgroup PaperKernel.paperThetaOneHom) =
      kernelSubgroup PaperKernel.paperThetaTwoHom :=
    kernelSubgroup_characteristic PaperKernel.paperThetaOneHom
      PaperKernel.paperThetaTwoHom f
  let σ := quotientAutomorphism PaperKernel.paperThetaOneHom
    PaperKernel.paperThetaTwoHom f hchar
  refine ⟨σ, ⟨LinearEquiv.ofBijective (paperModuleLinearMap f hchar)
    (paperModuleLinearMap_bijective f hchar)⟩⟩

/- The concrete Zhou groups are nonisomorphic from the first-module input (Zhou §6). -/
theorem paperNotIsomorphic
    (hOne : moduleOneSemisimple) :
    ¬ Nonempty
      (PaperKernel.paperGammaOneOf PaperKernel.paperActionData ≃*
        PaperKernel.paperGammaTwoOf PaperKernel.paperActionData) := by
  rintro ⟨f⟩
  obtain ⟨σ, ⟨e⟩⟩ := paperCharacteristicModuleEquiv f
  apply paper_moduleTwoAlong_not_semisimple σ
  exact e.isSemisimpleModule_iff.mp hOne

end
end PaperNonisomorphism
end Connes
