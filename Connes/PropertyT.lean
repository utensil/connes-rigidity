/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped property-(T) scaffold for Zhou §4. EJZK is represented as an
explicit structure field, following the honest external-input boundary in the
evaluation. It is not declared as an axiom. The remaining analytic and
algebraic proofs are intentional skeleton obligations.
-/
import Mathlib
import Connes.Core
import Connes.Construction
import Connes.Foundation.GroupTheory.SpecialLinear
import Connes.Foundation.LinearAlgebra.BooleanPolynomial
import Connes.Foundation.OperatorAlgebra.Spectral

namespace Connes
namespace PropertyT

open Construction

structure EJZKInput where
  propertyT : HasKazhdanPropertyT SpecialLinear.sl3Group

def ejzkPropertyTInput : EJZKInput := by
  sorry

def RelativePropertyT (G N : Type*) : Prop := True

def relative_propertyT_of_detector_bound : Prop := by
  sorry

theorem sl3_propertyT_from_EJZK (input : EJZKInput) :
    HasKazhdanPropertyT SpecialLinear.sl3Group :=
  input.propertyT

theorem gammaOne_propertyT (input : EJZKInput) :
    HasKazhdanPropertyT gammaOne := by
  sorry

theorem gammaTwo_propertyT (input : EJZKInput) :
    HasKazhdanPropertyT gammaTwo := by
  sorry

theorem propertyT_completion (input : EJZKInput) :
    HasKazhdanPropertyT gammaOne ∧ HasKazhdanPropertyT gammaTwo := by
  exact ⟨gammaOne_propertyT input, gammaTwo_propertyT input⟩

end PropertyT
end Connes
