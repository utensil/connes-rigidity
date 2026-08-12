/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

New paper-facing wrappers around Mathlib's semisimple-module API for Zhou §6.
The public OpenAI/ten-proofs work informed the decomposition boundary only;
this file is not copied from or imported from that project. The old product
equivalence is retained as a scaffold, while the exact-extension criterion
is now an explicit input rather than an implicit proof hole.
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

/-- Short linear extension data. Paper: §6. -/
structure LinearExtension
    (R M N E : Type*) [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E] where
  inclusion : M →ₗ[R] E
  projection : E →ₗ[R] N
  exact : Function.Exact inclusion projection

/-- Linear section of a short extension. Paper: §6. -/
structure LinearSection {R M N E : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (extension : LinearExtension R M N E) where
  section_ : N →ₗ[R] E
  projection_section : extension.projection.comp section_ = LinearMap.id

/-- Exact splitting witness. Paper: §6. -/
abbrev ExactSplits {R M N E : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (extension : LinearExtension R M N E) : Prop :=
  Nonempty (LinearSection extension)

/-- Extension-specific criterion turning semisimplicity into an exact split.
Paper: §6. -/
structure SemisimplicitySplittingCriterion
    {R M N E : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (extension : LinearExtension R M N E) where
  semisimple_splits : IsSemisimple R E → ExactSplits extension

/-- Section-retraction law in pointwise form. Paper: §6. -/
theorem LinearSection.projection_section_apply
    {R M N E : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    {extension : LinearExtension R M N E}
    (section_ : LinearSection extension) (n : N) :
    extension.projection (section_.section_ n) = n := by
  have h := LinearMap.congr_fun section_.projection_section n
  simpa using h

/-- Transport of semisimplicity. Paper: §6. -/
theorem semisimple_invariant_under_linear_equiv {R M N : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hM : IsSemisimple R M) : IsSemisimple R N := by
  letI : IsSemisimpleModule R M := hM
  exact IsSemisimpleModule.congr e.symm

/-- A proved product splitting transports semisimplicity to the extension.
Paper: §6. -/
theorem semisimple_of_splits {R M N E : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (h : Splits R M N E) (hprod : IsSemisimple R (M × N)) :
    IsSemisimple R E := by
  obtain ⟨e⟩ := h
  exact semisimple_invariant_under_linear_equiv e.symm hprod

/-- Nonsplit-extension obstruction. Paper: §6. -/
theorem nonsplit_extension_not_semisimple
    {R M N E : Type*}
    [Ring R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup E]
    [Module R M] [Module R N] [Module R E]
    (extension : LinearExtension R M N E)
    (h : ¬ ExactSplits extension)
    (criterion : SemisimplicitySplittingCriterion extension) :
    ¬ IsSemisimple R E := by
  intro hE
  exact h (criterion.semisimple_splits hE)

end Semisimple
end Connes
