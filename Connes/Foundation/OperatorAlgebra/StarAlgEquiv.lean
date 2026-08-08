/-
Copyright 2026 utensil
SPDX-License-Identifier: Apache-2.0

Proof transfer from OpenAI ten-proofs, ConnesRigidity.lean:30217-30246.
The source is cited for provenance only; this file has no dependency on it.
-/
import Mathlib
import Connes.Core

namespace Connes
namespace OpenAIPort

/-- Projection suprema are transported by star-algebra equivalences. Paper: §3. -/
theorem isProjectionSupremum_image_starAlgEquiv
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (p : A)
    (hp : IsProjectionSupremum S p) :
    IsProjectionSupremum (e '' S) (e p) := by
  refine ⟨hp.1.map e, ?_, ?_⟩
  · rintro q ⟨r, hrS, rfl⟩
    exact ⟨(hp.2.1 r hrS).1.map e,
      by
        simpa only [ProjectionLE, map_mul] using
          congrArg e (hp.2.1 r hrS).2⟩
  · intro r hr hupper
    have hr' : IsStarProjection (e.symm r) := hr.map e.symm
    have hbound : ∀ q ∈ S, ProjectionLE q (e.symm r) := by
      intro q hq
      have himage : e q ∈ e '' S := ⟨q, hq, rfl⟩
      have h := hupper (e q) himage
      simpa only [ProjectionLE, map_mul, StarAlgEquiv.symm_apply_apply] using congrArg e.symm h
    have hleast := hp.2.2 (e.symm r) hr' hbound
    simpa only [ProjectionLE, map_mul, StarAlgEquiv.apply_symm_apply] using congrArg e hleast

/-- Every star-algebra equivalence satisfies the normality interface. Paper: §3. -/
theorem starAlgEquiv_isNormal
    {A : Type u} {B : Type v}
    [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    IsNormalStarAlgEquiv e :=
  ⟨isProjectionSupremum_image_starAlgEquiv e,
    isProjectionSupremum_image_starAlgEquiv e.symm⟩

end OpenAIPort
end Connes
