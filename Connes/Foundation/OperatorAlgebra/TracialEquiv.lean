/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New standalone interfaces for normal trace-preserving factor equivalences.
The public OpenAI reference is used only for API comparison and attribution.
-/
import Mathlib
import Connes.Core
import Connes.Foundation.OperatorAlgebra.FactorEquiv

namespace Connes
namespace TracialEquiv

/-- Trace-preserving factor-equivalence predicate. Paper: §3. -/
def IsTracialEquivalence (G H : CountableDiscreteGroup) : Prop :=
  TracialGroupFactorsIsomorphic G H

/-- Reflexivity of the factor relation. Paper: §3. -/
theorem refl (G : CountableDiscreteGroup) : IsTracialEquivalence G G := by
  change TracialGroupFactorsIsomorphic G G
  exact ⟨OpenAIPort.groupFactorEquivRefl G⟩

/-- Symmetry of the factor relation. Paper: §3. -/
theorem symm {G H : CountableDiscreteGroup}
    (h : IsTracialEquivalence G H) : IsTracialEquivalence H G := by
  change TracialGroupFactorsIsomorphic G H at h
  change TracialGroupFactorsIsomorphic H G
  exact OpenAIPort.groupFactorsIsomorphic_symm h

/-- Transitivity of the factor relation. Paper: §3. -/
theorem trans {G H K : CountableDiscreteGroup}
    (hGH : IsTracialEquivalence G H) (hHK : IsTracialEquivalence H K) :
    IsTracialEquivalence G K := by
  change TracialGroupFactorsIsomorphic G H at hGH
  change TracialGroupFactorsIsomorphic H K at hHK
  change TracialGroupFactorsIsomorphic G K
  exact OpenAIPort.groupFactorsIsomorphic_trans hGH hHK

end TracialEquiv
end Connes
