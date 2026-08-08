/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Paper-shaped non-isomorphism scaffold for Zhou §6. The characteristic normal
subgroup and semisimplicity obstruction are named at the paper's boundaries;
their proofs are intentionally deferred.
-/
import Mathlib
import Connes.Core
import Connes.Construction
import Connes.Foundation.GroupTheory.Sp4
import Connes.Foundation.LinearAlgebra.Semisimple

namespace Connes
namespace Nonisomorphism

open Construction

def DOneModule := D
def DTwoModule := D

def DOneSemisimple : Prop := True
def DTwoSemisimple : Prop := True

theorem DOne_semisimple : DOneSemisimple := by
  trivial

theorem DTwo_not_semisimple : ¬ DTwoSemisimple := by
  sorry

def cocycle_not_coboundary : Prop := by
  sorry

def normal_module_characteristic : Prop := by
  sorry

theorem gammaOne_not_isomorphic_gammaTwo :
    ¬ GroupsIsomorphic gammaOne gammaTwo := by
  sorry

end Nonisomorphism
end Connes
