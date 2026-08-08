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

/-- Regular representation carrier. Paper: §3. -/
abbrev RegularRepresentation (G : Type*) [Group G] :=
  G →* unitary (GroupL2 G →L[ℂ] GroupL2 G)

/-- Regular representation boundary. Paper: §3. -/
noncomputable def regularRepresentation (G : Type*) [Group G] : RegularRepresentation G :=
  leftRegularRepresentation G

/-- Group-factor carrier. Paper: §3. -/
noncomputable def factor (G : CountableDiscreteGroup) :=
  GroupVonNeumannAlgebra G

/-- Canonical trace normalization. Paper: §3. -/
theorem canonicalTrace_identity (G : CountableDiscreteGroup) :
    canonicalTrace G ⟨1, by simp⟩ = 1 := by
  simp [canonicalTrace, delta]

end GroupFactor
end Connes
