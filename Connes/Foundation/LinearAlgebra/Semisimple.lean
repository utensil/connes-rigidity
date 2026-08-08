/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New paper-facing wrappers around Mathlib's semisimple-module API for Zhou §6.
The public OpenAI/ten-proofs work informed the decomposition boundary only;
this file is not copied from or imported from that project.
-/
import Mathlib

namespace Connes
namespace Semisimple

/-- Semisimplicity predicate wrapper. Paper: §6. -/
abbrev IsSemisimple (R M : Type*) [Ring R] [AddCommGroup M] [Module R M] : Prop :=
  IsSemisimpleModule R M

/-- Splitting witness boundary. Paper: §6. -/
def Splits (R M N E : Type*) [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E] : Prop :=
  Nonempty (E ≃ₗ[R] M × N)

/-- Transport of semisimplicity. Paper: §6. -/
theorem semisimple_invariant_under_linear_equiv {R M N : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hM : IsSemisimple R M) : IsSemisimple R N := by
  letI : IsSemisimpleModule R M := hM
  exact IsSemisimpleModule.congr e.symm

/-- Nonsplit-extension obstruction. Paper: §6. -/
theorem nonsplit_extension_not_semisimple {R M N E : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (h : ¬ Splits R M N E) : ¬ IsSemisimple R E := by
  sorry

end Semisimple
end Connes
