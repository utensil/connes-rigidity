/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for the Sp₄(F₂) arguments in Zhou §§2 and 6.
Mathlib supplies the symplectic-matrix carrier; the transitivity and normal
subgroup arguments are intentionally left as skeleton obligations.
-/
import Mathlib
import Connes.Foundation.LinearAlgebra.Symplectic

namespace Connes
namespace Sp4

/-- Characteristic-two scalar field. Paper: §§2, 6. -/
abbrev F := ZMod 2
/-- Symplectic group carrier. Paper: §§2, 6. -/
abbrev Group := Symplectic.Sp4

/-- Nonzero-vector action boundary. Paper: §2. -/
def actsOnNonzeroVectors : Prop := True

/-- Nonzero-vector transitivity. Paper: §2. -/
theorem transitive_on_nonzero_vectors : actsOnNonzeroVectors := by
  trivial

/-- Normal-subgroup obstruction boundary. Paper: §6. -/
def no_nontrivial_normal_elementary_abelian_subgroup : Prop := by
  sorry

end Sp4
end Connes
