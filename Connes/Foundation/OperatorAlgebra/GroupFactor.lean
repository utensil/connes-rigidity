/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New paper-facing wrappers for the group-factor vocabulary used in Zhou §3.
The shape is informed by the public OpenAI/ten-proofs Connes formalization at
commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, while all code here is
written for this standalone repository.
-/
import Mathlib
import Connes.Core

namespace Connes
namespace GroupFactor

abbrev RegularRepresentation (G : Type*) [Group G] :=
  G →* unitary (GroupL2 G →L[ℂ] GroupL2 G)

noncomputable def regularRepresentation (G : Type*) [Group G] : RegularRepresentation G :=
  leftRegularRepresentation G

noncomputable def factor (G : CountableDiscreteGroup) :=
  GroupVonNeumannAlgebra G

theorem canonicalTrace_identity (G : CountableDiscreteGroup) :
    canonicalTrace G ⟨1, by simp⟩ = 1 := by
  sorry

end GroupFactor
end Connes
